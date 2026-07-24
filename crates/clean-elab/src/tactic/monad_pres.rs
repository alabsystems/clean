// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `monad_pres` tactic for compositional state-field preservation proofs.
//!
//! The tactic targets equality goals of the form `s'.field = s.field` and
//! decomposes monadic `bind` chains into per-step preservation obligations.
//! Each step proves that the chosen field is preserved across one monadic
//! action, and the final proof is assembled with `Eq.trans`.

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::equality::replace_expr;
use super::tauto::fresh_hyp_name;

// =============================================================================
// Monadic pattern analysis
// =============================================================================

/// Recognized monadic computation patterns.
#[derive(Debug, Clone)]
pub(crate) enum MonadPattern {
    /// `Pure.pure a` / `pure a`
    Pure { value: Expr },
    /// `Bind.bind action continuation`
    Bind { action: Expr, continuation: Expr },
    /// `StateT.get`
    Get,
    /// `StateT.set s`
    Set { new_state: Expr },
    /// `StateT.modify f`
    Modify { modifier: Expr },
    /// `StateT.pure a` (kept separate for tactic-side pattern dispatch)
    Return { value: Expr },
}

const BIND_NAMES: &[&str] = &["Bind.bind", "bind", "StateT.bind"];
const PURE_NAMES: &[&str] = &["Pure", "Pure.pure", "pure"];
const RETURN_NAMES: &[&str] = &["StateT.pure"];
const GET_NAMES: &[&str] = &["get", "StateT.get"];
const SET_NAMES: &[&str] = &["set", "StateT.set"];
const MODIFY_NAMES: &[&str] = &["modify", "StateT.modify"];

fn name_matches(name: &Name, candidates: &[&str]) -> bool {
    let rendered = name.to_string();
    candidates
        .iter()
        .any(|candidate| rendered == *candidate || rendered.ends_with(candidate))
}

/// Analyze an expression and classify its monadic shape when recognized.
pub(crate) fn analyze_monad_expr(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Option<MonadPattern> {
    let expr = state.whnf(goal, expr);
    let head = expr.get_app_fn().clone();
    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, _) if name_matches(name, BIND_NAMES) => {
            if args.len() < 2 {
                return None;
            }
            Some(MonadPattern::Bind {
                action: args[args.len() - 2].clone(),
                continuation: args[args.len() - 1].clone(),
            })
        }
        ExprKind::Const(name, _) if name_matches(name, RETURN_NAMES) => args
            .last()
            .cloned()
            .map(|value| MonadPattern::Return { value }),
        ExprKind::Const(name, _) if name_matches(name, PURE_NAMES) => args
            .last()
            .cloned()
            .map(|value| MonadPattern::Pure { value }),
        ExprKind::Const(name, _) if name_matches(name, GET_NAMES) => Some(MonadPattern::Get),
        ExprKind::Const(name, _) if name_matches(name, SET_NAMES) => args
            .last()
            .cloned()
            .map(|new_state| MonadPattern::Set { new_state }),
        ExprKind::Const(name, _) if name_matches(name, MODIFY_NAMES) => args
            .last()
            .cloned()
            .map(|modifier| MonadPattern::Modify { modifier }),
        _ => None,
    }
}

// =============================================================================
// Case-split pattern analysis
// =============================================================================

const ITE_NAMES: &[&str] = &["ite", "Bool.ite"];
const DITE_NAMES: &[&str] = &["dite", "Bool.dite"];
// `Except.casesOn` is Lean-faithful (motive, major, then minors): the last
// three args of a full application are (scrut, err, ok). `Except.rec` keeps
// the legacy recursor layout (motive, minors, then major LAST): its last
// three args are (err, ok, scrut). The two spellings are matched separately
// in `match_case_split_head` so each reads its own positional layout.
const EXCEPT_CASES_ON_NAMES: &[&str] = &["Except.casesOn"];
const EXCEPT_REC_NAMES: &[&str] = &["Except.rec"];

/// Recognized case-split patterns inside monadic computations.
#[derive(Debug, Clone)]
pub(crate) enum CaseSplitPattern {
    /// `ite cond inst then_branch else_branch`
    Ite {
        cond: Expr,
        then_branch: Expr,
        else_branch: Expr,
    },
    /// `dite cond inst then_branch else_branch` (dependent)
    Dite {
        cond: Expr,
        then_branch: Expr,
        else_branch: Expr,
    },
    /// `Except.casesOn scrut err_handler ok_handler`
    ExceptCasesOn {
        scrut: Expr,
        ok_branch: Expr,
        err_branch: Expr,
    },
}

pub(crate) fn analyze_case_split(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Option<CaseSplitPattern> {
    // Try the surface form first (Wave 106). `ite` is registered as a
    // reducible `Definition` by `init_ite`, so calling `state.whnf` would
    // unfold it away and the structural matcher below would never fire.
    // Most case-split fixtures already write `ite` / `dite` /
    // `Except.casesOn` at the surface level, so we match on the original
    // spine head before any whnf is applied; only if the surface form is
    // unrecognised do we fall back to whnf for shapes that surface only
    // after reduction (e.g. abbreviations or projection-style monad
    // bindings).
    if let Some(pattern) = match_case_split_head(expr) {
        return Some(pattern);
    }
    let reduced = state.whnf(goal, expr);
    match_case_split_head(&reduced)
}

fn match_case_split_head(expr: &Expr) -> Option<CaseSplitPattern> {
    let head = expr.get_app_fn().clone();
    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();

    // Check dite BEFORE ite (Wave 91): `name_matches` uses `ends_with`,
    // so "dite" also satisfies the ITE suffix check. Putting the dite
    // arm first ensures structural recognition in a bare state where
    // the kernel `Decidable` predicate has not been initialised — the
    // instance arg is carried through the `Dite` pattern unmodified
    // for a later resolution stage.
    match head.kind() {
        ExprKind::Const(name, _) if name_matches(name, DITE_NAMES) && args.len() >= 4 => {
            Some(CaseSplitPattern::Dite {
                cond: args[args.len() - 4].clone(),
                then_branch: args[args.len() - 2].clone(),
                else_branch: args[args.len() - 1].clone(),
            })
        }
        ExprKind::Const(name, _) if name_matches(name, ITE_NAMES) && args.len() >= 4 => {
            Some(CaseSplitPattern::Ite {
                cond: args[args.len() - 4].clone(),
                then_branch: args[args.len() - 2].clone(),
                else_branch: args[args.len() - 1].clone(),
            })
        }
        ExprKind::Const(name, _)
            if name_matches(name, EXCEPT_CASES_ON_NAMES) && args.len() >= 3 =>
        {
            // Lean-faithful casesOn order: motive, (indices,) major, then
            // minors — the last three args are (scrut, err, ok).
            Some(CaseSplitPattern::ExceptCasesOn {
                scrut: args[args.len() - 3].clone(),
                err_branch: args[args.len() - 2].clone(),
                ok_branch: args[args.len() - 1].clone(),
            })
        }
        ExprKind::Const(name, _) if name_matches(name, EXCEPT_REC_NAMES) && args.len() >= 3 => {
            // `Except.rec` keeps the legacy layout (minors, then major LAST)
            // — the last three args are (err, ok, scrut).
            Some(CaseSplitPattern::ExceptCasesOn {
                scrut: args[args.len() - 1].clone(),
                err_branch: args[args.len() - 3].clone(),
                ok_branch: args[args.len() - 2].clone(),
            })
        }
        _ => None,
    }
}

// =============================================================================
// Equality / projection helpers
// =============================================================================

#[derive(Debug, Clone)]
enum FieldAccess {
    Proj {
        struct_name: Name,
        field_idx: u32,
        base: Expr,
    },
    App {
        head: Expr,
        prefix_args: Vec<Expr>,
        base: Expr,
    },
}

impl FieldAccess {
    fn base(&self) -> &Expr {
        match self {
            Self::Proj { base, .. } | Self::App { base, .. } => base,
        }
    }

    fn with_base(&self, base: Expr) -> Expr {
        match self {
            Self::Proj {
                struct_name,
                field_idx,
                ..
            } => Expr::proj(struct_name.clone(), *field_idx, base),
            Self::App {
                head, prefix_args, ..
            } => {
                let mut args = prefix_args.clone();
                args.push(base);
                Expr::apps(head.clone(), args)
            }
        }
    }

    fn same_field(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Proj {
                    struct_name: ln,
                    field_idx: li,
                    ..
                },
                Self::Proj {
                    struct_name: rn,
                    field_idx: ri,
                    ..
                },
            ) => ln == rn && li == ri,
            (
                Self::App {
                    head: lh,
                    prefix_args: la,
                    ..
                },
                Self::App {
                    head: rh,
                    prefix_args: ra,
                    ..
                },
            ) => lh == rh && la == ra,
            _ => false,
        }
    }

    fn field_name(&self) -> Option<String> {
        match self {
            Self::App { head, .. } => match head.kind() {
                ExprKind::Const(name, _) => Some(name.to_string()),
                _ => None,
            },
            Self::Proj { .. } => None,
        }
    }
}

fn name_tail(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn field_selected(field: &FieldAccess, field_names: &[Expr]) -> bool {
    if field_names.is_empty() {
        return true;
    }

    let Some(actual_name) = field.field_name() else {
        return true;
    };
    let actual_tail = name_tail(&actual_name);

    field_names.iter().any(|candidate| match candidate.kind() {
        ExprKind::Const(name, _) => {
            let rendered = name.to_string();
            rendered == actual_name
                || rendered == actual_tail
                || name_tail(&rendered) == actual_tail
                || actual_name.ends_with(&rendered)
        }
        _ => false,
    })
}

fn match_eq_expr(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let expr = state.whnf(goal, expr);
    let head = expr.get_app_fn().clone();
    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, _) if *name == Name::from_string("Eq") && args.len() == 3 => {
            Some((args[0].clone(), args[1].clone(), args[2].clone()))
        }
        _ => None,
    }
}

fn match_field_access(expr: &Expr) -> Option<FieldAccess> {
    match expr.kind() {
        ExprKind::Proj(struct_name, field_idx, base) => Some(FieldAccess::Proj {
            struct_name: struct_name.clone(),
            field_idx: *field_idx,
            base: (**base).clone(),
        }),
        ExprKind::MData(_, inner) => match_field_access(inner),
        _ => {
            let head = expr.get_app_fn().clone();
            let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();
            if args.is_empty() {
                return None;
            }
            match head.kind() {
                ExprKind::Const(_, _) => Some(FieldAccess::App {
                    head,
                    prefix_args: args[..args.len() - 1].to_vec(),
                    base: args[args.len() - 1].clone(),
                }),
                _ => None,
            }
        }
    }
}

fn mk_eq(alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [alpha, lhs, rhs],
    )
}

fn mk_eq_refl(alpha: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
        [alpha, value],
    )
}

fn mk_eq_trans(alpha: Expr, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.trans", vec![Level::succ(Level::zero())]),
        [alpha, a, b, c, hab, hbc],
    )
}

fn mk_prod_fst(pair: Expr) -> Expr {
    Expr::proj(Name::from_string("Prod"), 0, pair)
}

fn mk_prod_snd(pair: Expr) -> Expr {
    Expr::proj(Name::from_string("Prod"), 1, pair)
}

// =============================================================================
// Run-expression analysis
// =============================================================================

#[derive(Debug, Clone)]
enum RunStyle {
    StateTRun { head: Expr, prefix_args: Vec<Expr> },
    Direct,
}

impl RunStyle {
    fn apply(
        &self,
        state: &ProofState,
        goal: &Goal,
        action: &Expr,
        input_state: Expr,
    ) -> Option<Expr> {
        match self {
            Self::StateTRun { head, prefix_args } => {
                let alpha = extract_state_t_result_type(state, goal, action)?;
                let mut args = prefix_args.clone();
                args.push(alpha);
                args.push(action.clone());
                args.push(input_state);
                Some(Expr::apps(head.clone(), args))
            }
            Self::Direct => Some(Expr::app(action.clone(), input_state)),
        }
    }
}

#[derive(Debug, Clone)]
struct RunInvocation {
    style: RunStyle,
    computation: Expr,
    input_state: Expr,
}

#[derive(Debug, Clone)]
struct StepPlan {
    action: Expr,
    input_state: Expr,
    output_state: Expr,
}

#[derive(Debug, Clone)]
struct CaseSplitBranchPlan {
    computation: Expr,
    introduced_locals: Vec<LocalDecl>,
    plan: ChainPlan,
}

#[derive(Debug, Clone)]
struct CaseSplitPlan {
    split_expr: Expr,
    pattern: CaseSplitPattern,
    branches: Vec<CaseSplitBranchPlan>,
}

#[derive(Debug, Clone)]
enum ChainTail {
    Step(StepPlan),
    CaseSplit(CaseSplitPlan),
}

#[derive(Debug, Clone)]
struct ChainPlan {
    prefix_steps: Vec<StepPlan>,
    tail: ChainTail,
}

fn is_prod_type(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    let ty = state.whnf(goal, ty);
    let head = ty.get_app_fn().clone();
    let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
    matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Prod"))
        && args.len() == 2
}

fn extract_pair_payload_expr(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    let ty = state.infer_type(goal, expr).ok()?;
    if is_prod_type(state, goal, &ty) {
        return Some(expr.clone());
    }

    match expr.kind() {
        ExprKind::App(_, arg) => extract_pair_payload_expr(state, goal, arg),
        ExprKind::MData(_, inner) => extract_pair_payload_expr(state, goal, inner),
        _ => None,
    }
}

fn extract_result_value_expr(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    extract_pair_payload_expr(state, goal, expr).map(mk_prod_fst)
}

fn extract_output_state_expr(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    extract_pair_payload_expr(state, goal, expr).map(mk_prod_snd)
}

fn extract_state_t_result_type(state: &ProofState, goal: &Goal, action: &Expr) -> Option<Expr> {
    let ty = state.infer_type(goal, action).ok()?;
    let ty = state.whnf(goal, &ty);
    let head = ty.get_app_fn().clone();
    let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, _) if name.to_string().ends_with("StateT") && args.len() >= 3 => {
            Some(args[2].clone())
        }
        ExprKind::Const(name, _) if *name == Name::from_string("StateT") && args.len() >= 3 => {
            Some(args[2].clone())
        }
        _ => None,
    }
}

fn parse_run_invocation(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<RunInvocation> {
    let expr = state.whnf(goal, expr);
    let head = expr.get_app_fn().clone();
    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();

    if let ExprKind::Const(name, _) = head.kind() {
        if name.to_string().ends_with("StateT.run") && args.len() >= 5 {
            return Some(RunInvocation {
                style: RunStyle::StateTRun {
                    head,
                    prefix_args: args[..args.len() - 3].to_vec(),
                },
                computation: args[args.len() - 2].clone(),
                input_state: args[args.len() - 1].clone(),
            });
        }
    }

    if args.is_empty() {
        return None;
    }

    if extract_pair_payload_expr(state, goal, &expr).is_some() {
        let input_state = args[args.len() - 1].clone();
        let computation = if args.len() == 1 {
            head
        } else {
            Expr::apps(head, args[..args.len() - 1].to_vec())
        };
        return Some(RunInvocation {
            style: RunStyle::Direct,
            computation,
            input_state,
        });
    }

    None
}

fn continuation_body(
    state: &ProofState,
    goal: &Goal,
    continuation: &Expr,
    value: &Expr,
) -> Option<Expr> {
    let continuation = state.whnf(goal, continuation);
    match continuation.kind() {
        ExprKind::Lam(_, _, body) => Some(body.instantiate(value)),
        ExprKind::MData(_, inner) => continuation_body(state, goal, inner, value),
        _ => None,
    }
}

fn plan_action_step(
    state: &ProofState,
    goal: &Goal,
    style: &RunStyle,
    action: &Expr,
    input_state: &Expr,
    known_output_state: Option<Expr>,
) -> Option<(StepPlan, Expr)> {
    let pattern = analyze_monad_expr(state, goal, action);
    let run_expr = style.apply(state, goal, action, input_state.clone());

    let result_value = match &pattern {
        Some(MonadPattern::Pure { value }) | Some(MonadPattern::Return { value }) => value.clone(),
        Some(MonadPattern::Get) => input_state.clone(),
        _ => extract_result_value_expr(state, goal, run_expr.as_ref()?)?,
    };

    let output_state = if let Some(known) = known_output_state {
        known
    } else {
        match pattern {
            Some(MonadPattern::Pure { .. })
            | Some(MonadPattern::Return { .. })
            | Some(MonadPattern::Get) => input_state.clone(),
            Some(MonadPattern::Set { new_state }) => new_state,
            Some(MonadPattern::Modify { modifier }) => Expr::app(modifier, input_state.clone()),
            _ => extract_output_state_expr(state, goal, run_expr.as_ref()?)?,
        }
    };

    Some((
        StepPlan {
            action: action.clone(),
            input_state: input_state.clone(),
            output_state,
        },
        result_value,
    ))
}

fn mk_false() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn mk_not(prop: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, prop, mk_false())
}

fn abstract_over_locals(mut expr: Expr, locals: &[LocalDecl]) -> Expr {
    for decl in locals.iter().rev() {
        expr = Expr::lam(
            BinderInfo::Default,
            decl.ty.clone(),
            expr.abstract_fvar(decl.fvar),
        );
    }
    expr
}

fn make_case_local_decl(state: &mut ProofState, goal: &Goal, base: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        fvar: state.fresh_fvar(),
        name: fresh_hyp_name(&goal.local_ctx, base),
        ty,
        value: None,
    }
}

fn open_lambda_with_local(
    state: &mut ProofState,
    goal: &Goal,
    expr: &Expr,
    base: &str,
) -> Option<(LocalDecl, Expr)> {
    let expr = state.whnf(goal, expr);
    match expr.kind() {
        ExprKind::Lam(_, ty, body) => {
            let local = make_case_local_decl(state, goal, base, ty.as_ref().clone());
            Some((local.clone(), body.instantiate(&Expr::fvar(local.fvar))))
        }
        ExprKind::MData(_, inner) => open_lambda_with_local(state, goal, inner, base),
        _ => None,
    }
}

fn collect_case_split_branch(
    state: &mut ProofState,
    goal: &Goal,
    style: &RunStyle,
    input_state: &Expr,
    known_result_expr: Option<Expr>,
    computation: Expr,
    introduced_locals: Vec<LocalDecl>,
) -> Option<CaseSplitBranchPlan> {
    let mut branch_goal = goal.clone();
    branch_goal
        .local_ctx
        .extend(introduced_locals.iter().cloned());
    let plan = collect_chain_steps(
        state,
        &branch_goal,
        style,
        &computation,
        input_state.clone(),
        known_result_expr,
    )?;
    Some(CaseSplitBranchPlan {
        computation,
        introduced_locals,
        plan,
    })
}

fn collect_case_split_plan(
    state: &mut ProofState,
    goal: &Goal,
    style: &RunStyle,
    split_expr: &Expr,
    input_state: Expr,
    known_result_expr: Option<Expr>,
    pattern: CaseSplitPattern,
) -> Option<CaseSplitPlan> {
    let branches = match &pattern {
        CaseSplitPattern::Ite {
            cond,
            then_branch,
            else_branch,
        } => {
            let neg_cond = mk_not(cond.clone());
            let then_local = make_case_local_decl(state, goal, "h_monad_pres", cond.clone());
            let else_local = make_case_local_decl(state, goal, "h_not_monad_pres", neg_cond);
            let then_computation = state.whnf(goal, then_branch);
            let else_computation = state.whnf(goal, else_branch);
            vec![
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &then_computation)),
                    then_computation,
                    vec![then_local],
                )?,
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &else_computation)),
                    else_computation,
                    vec![else_local],
                )?,
            ]
        }
        CaseSplitPattern::Dite {
            then_branch,
            else_branch,
            ..
        } => {
            let (then_local, then_computation) =
                open_lambda_with_local(state, goal, then_branch, "h_monad_pres")?;
            let (else_local, else_computation) =
                open_lambda_with_local(state, goal, else_branch, "h_not_monad_pres")?;
            vec![
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &then_computation)),
                    then_computation,
                    vec![then_local],
                )?,
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &else_computation)),
                    else_computation,
                    vec![else_local],
                )?,
            ]
        }
        CaseSplitPattern::ExceptCasesOn {
            ok_branch,
            err_branch,
            ..
        } => {
            let (ok_local, ok_computation) =
                open_lambda_with_local(state, goal, ok_branch, "ok_monad_pres")?;
            let (err_local, err_computation) =
                open_lambda_with_local(state, goal, err_branch, "err_monad_pres")?;
            vec![
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &ok_computation)),
                    ok_computation,
                    vec![ok_local],
                )?,
                collect_case_split_branch(
                    state,
                    goal,
                    style,
                    &input_state,
                    known_result_expr
                        .as_ref()
                        .map(|expr| replace_expr(expr, split_expr, &err_computation)),
                    err_computation,
                    vec![err_local],
                )?,
            ]
        }
    };

    Some(CaseSplitPlan {
        split_expr: split_expr.clone(),
        pattern,
        branches,
    })
}

fn collect_chain_steps(
    state: &mut ProofState,
    goal: &Goal,
    style: &RunStyle,
    computation: &Expr,
    input_state: Expr,
    known_result_expr: Option<Expr>,
) -> Option<ChainPlan> {
    match analyze_monad_expr(state, goal, computation) {
        Some(MonadPattern::Bind {
            action,
            continuation,
        }) => {
            let (step, value) = plan_action_step(state, goal, style, &action, &input_state, None)?;
            let next_computation = continuation_body(state, goal, &continuation, &value)?;
            let mut rest = collect_chain_steps(
                state,
                goal,
                style,
                &next_computation,
                step.output_state.clone(),
                known_result_expr,
            )?;
            rest.prefix_steps.insert(0, step);
            Some(rest)
        }
        Some(_) => {
            let known_output = known_result_expr
                .as_ref()
                .and_then(|expr| extract_output_state_expr(state, goal, expr));
            let (step, _) =
                plan_action_step(state, goal, style, computation, &input_state, known_output)?;
            Some(ChainPlan {
                prefix_steps: Vec::new(),
                tail: ChainTail::Step(step),
            })
        }
        None => {
            if let Some(pattern) = analyze_case_split(state, goal, computation) {
                let case_split = collect_case_split_plan(
                    state,
                    goal,
                    style,
                    computation,
                    input_state,
                    known_result_expr,
                    pattern,
                )?;
                Some(ChainPlan {
                    prefix_steps: Vec::new(),
                    tail: ChainTail::CaseSplit(case_split),
                })
            } else {
                let known_output = known_result_expr
                    .as_ref()
                    .and_then(|expr| extract_output_state_expr(state, goal, expr));
                let (step, _) =
                    plan_action_step(state, goal, style, computation, &input_state, known_output)?;
                Some(ChainPlan {
                    prefix_steps: Vec::new(),
                    tail: ChainTail::Step(step),
                })
            }
        }
    }
}

fn try_chain_from_run(
    state: &mut ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
    field: &FieldAccess,
    run_expr: &Expr,
    result_expr: Option<Expr>,
) -> Option<ChainPlan> {
    let invocation = parse_run_invocation(state, goal, run_expr)?;
    let rhs_field = field.with_base(invocation.input_state.clone());
    if !state.is_def_eq(goal, &rhs_field, rhs) {
        return None;
    }

    let chain = collect_chain_steps(
        state,
        goal,
        &invocation.style,
        &invocation.computation,
        invocation.input_state,
        result_expr.or_else(|| Some(run_expr.clone())),
    )?;

    match &chain.tail {
        ChainTail::Step(step) => {
            let lhs_field = field.with_base(step.output_state.clone());
            if state.is_def_eq(goal, &lhs_field, lhs) {
                Some(chain)
            } else {
                None
            }
        }
        ChainTail::CaseSplit(_) => Some(chain),
    }
}

fn find_chain_plan(
    state: &mut ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
    field: &FieldAccess,
) -> Option<ChainPlan> {
    match field.base().kind() {
        ExprKind::App(func, arg) => {
            if let ExprKind::Const(name, _) = func.kind() {
                if name.to_string().ends_with("Prod.snd") {
                    if let Some(chain) = try_chain_from_run(state, goal, lhs, rhs, field, arg, None)
                    {
                        return Some(chain);
                    }
                }
            }
        }
        ExprKind::Proj(struct_name, 1, arg) if *struct_name == Name::from_string("Prod") => {
            if let Some(chain) = try_chain_from_run(state, goal, lhs, rhs, field, arg, None) {
                return Some(chain);
            }
        }
        _ => {}
    }

    for local in &goal.local_ctx {
        let local_ty = state.metas.instantiate(&local.ty);
        let Some((_, hyp_lhs, hyp_rhs)) = match_eq_expr(state, goal, &local_ty) else {
            continue;
        };

        if let Some(chain) = try_chain_from_run(
            state,
            goal,
            lhs,
            rhs,
            field,
            &hyp_lhs,
            Some(hyp_rhs.clone()),
        ) {
            return Some(chain);
        }

        if let Some(chain) = try_chain_from_run(
            state,
            goal,
            lhs,
            rhs,
            field,
            &hyp_rhs,
            Some(hyp_lhs.clone()),
        ) {
            return Some(chain);
        }
    }

    None
}

// =============================================================================
// Proof construction
// =============================================================================

fn step_proof_or_goal(
    state: &mut ProofState,
    goal: &Goal,
    eq_ty: &Expr,
    field: &FieldAccess,
    next_step_idx: &mut usize,
    step: &StepPlan,
) -> (Expr, Option<Goal>) {
    let step_idx = *next_step_idx;
    *next_step_idx += 1;
    let lhs = field.with_base(step.output_state.clone());
    let rhs = field.with_base(step.input_state.clone());

    if state.is_def_eq(goal, &lhs, &rhs) {
        return (mk_eq_refl(eq_ty.clone(), rhs), None);
    }

    let step_target = mk_eq(eq_ty.clone(), lhs, rhs);
    let step_meta_id = state.fresh_meta_in_context(step_target.clone(), &goal.local_ctx);
    let step_meta = Expr::fvar(MetaState::to_fvar(step_meta_id));

    (
        step_meta,
        Some(Goal {
            meta_id: step_meta_id,
            target: step_target,
            local_ctx: goal.local_ctx.clone(),
            tag: Some(format!("monad_pres.step_{step_idx}")),
        }),
    )
}

/// Compose step proofs `f(s₁)=f(s₀), ..., f(sₙ)=f(sₙ₋₁)` into `f(sₙ)=f(s₀)`.
fn compose_preservation_proof(eq_ty: Expr, boundary_fields: &[Expr], step_proofs: &[Expr]) -> Expr {
    if step_proofs.is_empty() {
        return mk_eq_refl(eq_ty, boundary_fields[0].clone());
    }

    let final_field = boundary_fields[boundary_fields.len() - 1].clone();
    let mut proof = step_proofs[step_proofs.len() - 1].clone();

    for i in (0..step_proofs.len() - 1).rev() {
        proof = mk_eq_trans(
            eq_ty.clone(),
            final_field.clone(),
            boundary_fields[i + 1].clone(),
            boundary_fields[i].clone(),
            proof,
            step_proofs[i].clone(),
        );
    }

    proof
}

fn extend_goal(goal: &Goal, target: Expr, introduced_locals: &[LocalDecl]) -> Goal {
    let mut local_ctx = goal.local_ctx.clone();
    local_ctx.extend(introduced_locals.iter().cloned());
    Goal {
        meta_id: goal.meta_id,
        target,
        local_ctx,
        tag: goal.tag.clone(),
    }
}

fn build_linear_chain_proof(
    state: &mut ProofState,
    goal: &Goal,
    eq_ty: &Expr,
    field: &FieldAccess,
    rhs_field: &Expr,
    steps: &[StepPlan],
    next_step_idx: &mut usize,
) -> (Option<Expr>, Vec<Goal>, Expr) {
    if steps.is_empty() {
        return (None, Vec::new(), rhs_field.clone());
    }

    let mut step_proofs = Vec::with_capacity(steps.len());
    let mut pending_goals = Vec::new();
    for step in steps {
        let (proof, pending) = step_proof_or_goal(state, goal, eq_ty, field, next_step_idx, step);
        step_proofs.push(proof);
        if let Some(pending) = pending {
            pending_goals.push(pending);
        }
    }

    let mut boundary_fields = Vec::with_capacity(steps.len() + 1);
    boundary_fields.push(rhs_field.clone());
    for step in steps {
        boundary_fields.push(field.with_base(step.output_state.clone()));
    }

    let last_field = boundary_fields
        .last()
        .cloned()
        .unwrap_or_else(|| rhs_field.clone());
    (
        Some(compose_preservation_proof(
            eq_ty.clone(),
            &boundary_fields,
            &step_proofs,
        )),
        pending_goals,
        last_field,
    )
}

fn build_or_case_motive(
    state: &mut ProofState,
    cond: &Expr,
    neg_cond: &Expr,
    then_target: &Expr,
    then_locals: &[LocalDecl],
    else_target: &Expr,
    else_locals: &[LocalDecl],
) -> Expr {
    let or_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), cond.clone()),
        neg_cond.clone(),
    );
    let motive_sort = Expr::lam(BinderInfo::Default, or_ty.clone(), Expr::prop());
    let inner_then = abstract_over_locals(then_target.clone(), then_locals);
    let inner_else = abstract_over_locals(else_target.clone(), else_locals);
    let or_case_fvar = state.fresh_fvar();
    let motive_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Or.rec"), vec![]),
                            cond.clone(),
                        ),
                        neg_cond.clone(),
                    ),
                    motive_sort,
                ),
                inner_then,
            ),
            inner_else,
        ),
        Expr::fvar(or_case_fvar),
    );

    Expr::lam(
        BinderInfo::Default,
        or_ty,
        motive_body.abstract_fvar(or_case_fvar),
    )
}

fn build_or_case_proof_term(
    state: &mut ProofState,
    cond: &Expr,
    then_target: &Expr,
    then_locals: &[LocalDecl],
    then_proof: Expr,
    else_target: &Expr,
    else_locals: &[LocalDecl],
    else_proof: Expr,
) -> Expr {
    let neg_cond = mk_not(cond.clone());
    let motive = build_or_case_motive(
        state,
        cond,
        &neg_cond,
        then_target,
        then_locals,
        else_target,
        else_locals,
    );
    let branch_pos = abstract_over_locals(then_proof, then_locals);
    let branch_neg = abstract_over_locals(else_proof, else_locals);
    let em_app = Expr::app(
        Expr::const_(Name::from_string("Classical.em"), vec![]),
        cond.clone(),
    );

    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Or.rec"), vec![]),
                            cond.clone(),
                        ),
                        neg_cond,
                    ),
                    motive,
                ),
                branch_pos,
            ),
            branch_neg,
        ),
        em_app,
    )
}

fn build_except_case_proof_term(
    state: &mut ProofState,
    goal: &Goal,
    plan: &CaseSplitPlan,
    ok_proof: Expr,
    err_proof: Expr,
) -> Result<Expr, TacticError> {
    let CaseSplitPattern::ExceptCasesOn {
        scrut,
        ok_branch,
        err_branch,
    } = &plan.pattern
    else {
        return Err(TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "expected Except.casesOn case split".into(),
        });
    };

    let split_expr = state.whnf(goal, &plan.split_expr);
    let head = split_expr.get_app_fn().clone();
    let mut args: Vec<Expr> = split_expr.get_app_args().into_iter().cloned().collect();
    if args.len() < 4 {
        return Err(TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "Except.casesOn application is missing motive or handlers".into(),
        });
    }

    let scrut_pos =
        args.iter()
            .rposition(|arg| arg == scrut)
            .ok_or_else(|| TacticError::InvalidTarget {
                tactic: "monad_pres".into(),
                detail: "Except.casesOn scrutinee could not be located".into(),
            })?;
    let err_pos = args
        .iter()
        .rposition(|arg| arg == err_branch)
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "Except.casesOn error handler could not be located".into(),
        })?;
    let ok_pos = args
        .iter()
        .rposition(|arg| arg == ok_branch)
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "Except.casesOn ok handler could not be located".into(),
        })?;
    let first_special = scrut_pos.min(err_pos).min(ok_pos);
    if first_special == 0 {
        return Err(TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "Except.casesOn application is missing motive".into(),
        });
    }
    let motive_pos = first_special - 1;
    let scrut_ty = state.infer_type(goal, scrut)?;
    let major_fvar = state.fresh_fvar();

    let mut generic_args = args.clone();
    generic_args[scrut_pos] = Expr::fvar(major_fvar);
    let generic_split_expr = Expr::apps(head.clone(), generic_args);
    let motive_body = replace_expr(&goal.target, &plan.split_expr, &generic_split_expr);
    let motive = Expr::lam(
        BinderInfo::Default,
        scrut_ty,
        motive_body.abstract_fvar(major_fvar),
    );
    args[motive_pos] = motive;
    args[err_pos] = err_proof;
    args[ok_pos] = ok_proof;
    Ok(Expr::apps(head, args))
}

fn build_case_split_proof(
    state: &mut ProofState,
    goal: &Goal,
    field: &FieldAccess,
    plan: &CaseSplitPlan,
    next_step_idx: &mut usize,
) -> Result<(Expr, Vec<Goal>), TacticError> {
    match &plan.pattern {
        CaseSplitPattern::Ite { cond, .. } | CaseSplitPattern::Dite { cond, .. } => {
            let then_branch = &plan.branches[0];
            let else_branch = &plan.branches[1];
            let then_target =
                replace_expr(&goal.target, &plan.split_expr, &then_branch.computation);
            let else_target =
                replace_expr(&goal.target, &plan.split_expr, &else_branch.computation);
            let then_goal = extend_goal(goal, then_target, &then_branch.introduced_locals);
            let else_goal = extend_goal(goal, else_target, &else_branch.introduced_locals);
            let (then_proof, mut then_pending) =
                build_chain_proof(state, &then_goal, field, &then_branch.plan, next_step_idx)?;
            let (else_proof, mut else_pending) =
                build_chain_proof(state, &else_goal, field, &else_branch.plan, next_step_idx)?;
            let proof = build_or_case_proof_term(
                state,
                cond,
                &then_goal.target,
                &then_branch.introduced_locals,
                then_proof,
                &else_goal.target,
                &else_branch.introduced_locals,
                else_proof,
            );
            let mut pending_goals = Vec::new();
            pending_goals.append(&mut then_pending);
            pending_goals.append(&mut else_pending);
            Ok((proof, pending_goals))
        }
        CaseSplitPattern::ExceptCasesOn { .. } => {
            let ok_branch = &plan.branches[0];
            let err_branch = &plan.branches[1];
            let ok_target = replace_expr(&goal.target, &plan.split_expr, &ok_branch.computation);
            let err_target = replace_expr(&goal.target, &plan.split_expr, &err_branch.computation);
            let ok_goal = extend_goal(goal, ok_target, &ok_branch.introduced_locals);
            let err_goal = extend_goal(goal, err_target, &err_branch.introduced_locals);
            let (ok_proof, mut ok_pending) =
                build_chain_proof(state, &ok_goal, field, &ok_branch.plan, next_step_idx)?;
            let (err_proof, mut err_pending) =
                build_chain_proof(state, &err_goal, field, &err_branch.plan, next_step_idx)?;
            let proof = build_except_case_proof_term(
                state,
                goal,
                plan,
                abstract_over_locals(ok_proof, &ok_branch.introduced_locals),
                abstract_over_locals(err_proof, &err_branch.introduced_locals),
            )?;
            let mut pending_goals = Vec::new();
            pending_goals.append(&mut ok_pending);
            pending_goals.append(&mut err_pending);
            Ok((proof, pending_goals))
        }
    }
}

fn build_chain_proof(
    state: &mut ProofState,
    goal: &Goal,
    field: &FieldAccess,
    chain: &ChainPlan,
    next_step_idx: &mut usize,
) -> Result<(Expr, Vec<Goal>), TacticError> {
    let (eq_ty, lhs, rhs) =
        match_eq_expr(state, goal, &goal.target).ok_or_else(|| TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "goal is not an equality".into(),
        })?;

    match &chain.tail {
        ChainTail::Step(step) => {
            let mut all_steps = chain.prefix_steps.clone();
            all_steps.push(step.clone());
            let (proof, pending_goals, _) = build_linear_chain_proof(
                state,
                goal,
                &eq_ty,
                field,
                &rhs,
                &all_steps,
                next_step_idx,
            );
            Ok((
                proof.unwrap_or_else(|| mk_eq_refl(eq_ty.clone(), rhs.clone())),
                pending_goals,
            ))
        }
        ChainTail::CaseSplit(case_split) => {
            let (prefix_proof, mut pending_goals, split_input_field) = build_linear_chain_proof(
                state,
                goal,
                &eq_ty,
                field,
                &rhs,
                &chain.prefix_steps,
                next_step_idx,
            );
            let tail_goal = Goal {
                meta_id: goal.meta_id,
                target: mk_eq(eq_ty.clone(), lhs.clone(), split_input_field.clone()),
                local_ctx: goal.local_ctx.clone(),
                tag: goal.tag.clone(),
            };
            let (tail_proof, mut tail_pending) =
                build_case_split_proof(state, &tail_goal, field, case_split, next_step_idx)?;
            pending_goals.append(&mut tail_pending);

            let proof = if let Some(prefix_proof) = prefix_proof {
                mk_eq_trans(eq_ty, lhs, split_input_field, rhs, tail_proof, prefix_proof)
            } else {
                tail_proof
            };
            Ok((proof, pending_goals))
        }
    }
}

fn try_refl_close(state: &mut ProofState, goal: &Goal, eq_ty: &Expr, rhs: &Expr) -> TacticResult {
    let proof = mk_eq_refl(eq_ty.clone(), rhs.clone());
    state
        .close_goal(goal, proof)
        .map_err(|_| TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "goal is not definitionally reflexive and no monadic chain was found".into(),
        })
}

// =============================================================================
// Main tactic
// =============================================================================

/// Prove state-field preservation by splitting a monadic bind chain into steps.
pub(crate) fn monad_pres(state: &mut ProofState, field_names: &[Expr]) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let (eq_ty, lhs, rhs) =
        match_eq_expr(state, &goal, &goal.target).ok_or_else(|| TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "goal is not an equality".into(),
        })?;

    let lhs_field = match_field_access(&lhs).ok_or_else(|| TacticError::InvalidTarget {
        tactic: "monad_pres".into(),
        detail: "left-hand side is not a recognizable state field projection".into(),
    })?;
    let rhs_field = match_field_access(&rhs).ok_or_else(|| TacticError::InvalidTarget {
        tactic: "monad_pres".into(),
        detail: "right-hand side is not a recognizable state field projection".into(),
    })?;

    if !lhs_field.same_field(&rhs_field) {
        return Err(TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "goal does not compare the same field on both sides".into(),
        });
    }

    if !field_selected(&lhs_field, field_names) {
        return Err(TacticError::InvalidTarget {
            tactic: "monad_pres".into(),
            detail: "goal field does not match the fields requested by monad_pres".into(),
        });
    }

    let Some(chain) = find_chain_plan(state, &goal, &lhs, &rhs, &lhs_field) else {
        return try_refl_close(state, &goal, &eq_ty, &rhs);
    };

    let mut next_step_idx = 0;
    let (proof, pending_goals) =
        build_chain_proof(state, &goal, &lhs_field, &chain, &mut next_step_idx)?;
    state.close_goal(&goal, proof)?;

    for pending in pending_goals.into_iter().rev() {
        state.goals.push_front(pending);
    }

    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Environment};

    fn setup_env() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_prod().expect("init_prod");
        env.init_punit().expect("init_punit");

        env.add_decl(Declaration::Axiom {
            name: Name::from_string("S"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("state type");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("R"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("result type");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("M"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        })
        .expect("monad type");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("s"),
            level_params: vec![],
            type_: Expr::const_str("S"),
        })
        .expect("input state");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("s'"),
            level_params: vec![],
            type_: Expr::const_str("S"),
        })
        .expect("output state");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("S.memory"),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str("S"), Expr::const_str("R")),
        })
        .expect("field accessor");

        env
    }

    fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .expect(name);
    }

    fn state_t_monad() -> Expr {
        Expr::apps(
            Expr::const_str("StateT"),
            [Expr::const_str("S"), Expr::const_str("M")],
        )
    }

    fn state_t_ty() -> Expr {
        Expr::apps(
            Expr::const_str("StateT"),
            [
                Expr::const_str("S"),
                Expr::const_str("M"),
                Expr::const_str("R"),
            ],
        )
    }

    fn prod_r_s() -> Expr {
        Expr::apps(
            Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
            [Expr::const_str("R"), Expr::const_str("S")],
        )
    }

    fn mk_memory(base: Expr) -> Expr {
        Expr::app(Expr::const_str("S.memory"), base)
    }

    fn mk_pure(value: Expr) -> Expr {
        Expr::apps(
            Expr::const_str("Pure.pure"),
            [state_t_monad(), Expr::const_str("R"), value],
        )
    }

    fn mk_bind(action: Expr, continuation: Expr) -> Expr {
        Expr::apps(
            Expr::const_str("Bind.bind"),
            [
                state_t_monad(),
                Expr::const_str("R"),
                Expr::const_str("R"),
                action,
                continuation,
            ],
        )
    }

    fn mk_state_t_run(computation: Expr, input_state: Expr) -> Expr {
        Expr::apps(
            Expr::const_str("StateT.run"),
            [
                Expr::const_str("S"),
                Expr::const_str("M"),
                Expr::const_str("R"),
                computation,
                input_state,
            ],
        )
    }

    fn mk_ite(then_branch: Expr, else_branch: Expr) -> Expr {
        // `ite.{u}` is registered with one universe parameter (see
        // `init_ite`); fixtures pin `u := 1` so `Sort u = Type` (the
        // `StateT` value's sort) and the kernel level-count check on
        // `close_goal` is satisfied. `analyze_case_split` matches the
        // surface form before whnf (Wave 106), so providing the real
        // level does not cause the reducible `ite` definition to
        // unfold under us.
        Expr::apps(
            Expr::const_str_levels("ite", vec![Level::succ(Level::zero())]),
            [
                state_t_ty(),
                Expr::const_str("cond"),
                Expr::const_str("instCond"),
                then_branch,
                else_branch,
            ],
        )
    }

    fn mk_dite(then_branch: Expr, else_branch: Expr) -> Expr {
        // See `mk_ite`. `dite.{u}` has the same level arity.
        Expr::apps(
            Expr::const_str_levels("dite", vec![Level::succ(Level::zero())]),
            [
                state_t_ty(),
                Expr::const_str("cond"),
                Expr::const_str("instCond"),
                then_branch,
                else_branch,
            ],
        )
    }

    fn mk_except_cases_on(scrutinee: Expr, error_branch: Expr, ok_branch: Expr) -> Expr {
        Expr::apps(
            Expr::const_str("Except.casesOn"),
            [
                Expr::const_str("motive"),
                scrutinee,
                error_branch,
                ok_branch,
            ],
        )
    }

    fn setup_state_t_env() -> Environment {
        let mut env = setup_env();
        env.init_ite().expect("init_ite");
        // `init_classical` also pulls in `Or`/`Or.rec`/`Classical.em`,
        // which `build_or_case_proof_term` produces when discharging the
        // case-split.
        env.init_classical().expect("init_classical");

        add_axiom(
            &mut env,
            "StateT",
            Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                    Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                ),
            ),
        );

        add_axiom(
            &mut env,
            "Pure.pure",
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::pi(BinderInfo::Default, Expr::const_str("R"), state_t_ty()),
                ),
            ),
        );

        add_axiom(
            &mut env,
            "Bind.bind",
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::type_(),
                        Expr::pi(
                            BinderInfo::Default,
                            state_t_ty(),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::arrow(Expr::const_str("R"), state_t_ty()),
                                state_t_ty(),
                            ),
                        ),
                    ),
                ),
            ),
        );

        add_axiom(
            &mut env,
            "StateT.run",
            Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::type_(),
                        Expr::pi(
                            BinderInfo::Default,
                            state_t_ty(),
                            Expr::pi(BinderInfo::Default, Expr::const_str("S"), prod_r_s()),
                        ),
                    ),
                ),
            ),
        );

        add_axiom(&mut env, "action", state_t_ty());
        add_axiom(&mut env, "cond", Expr::prop());
        add_axiom(
            &mut env,
            "instCond",
            Expr::app(Expr::const_str("Decidable"), Expr::const_str("cond")),
        );

        env
    }

    fn build_bind_case_split_fixture() -> (Expr, Expr, Expr, Expr, Expr) {
        let action = Expr::const_str("action");
        let action_run = mk_state_t_run(action.clone(), Expr::const_str("s"));
        let action_value = mk_prod_fst(action_run.clone());
        let action_state = mk_prod_snd(action_run);
        let continuation = Expr::lam(
            BinderInfo::Default,
            Expr::const_str("R"),
            mk_ite(mk_pure(Expr::bvar(0)), mk_pure(Expr::bvar(0))),
        );
        let bind_expr = mk_bind(action, continuation);
        let bind_run = mk_state_t_run(bind_expr.clone(), Expr::const_str("s"));
        let final_state = mk_prod_snd(bind_run);
        let case_split_action = mk_ite(mk_pure(action_value.clone()), mk_pure(action_value));
        let target = mk_eq(
            Expr::const_str("R"),
            mk_memory(final_state.clone()),
            mk_memory(Expr::const_str("s")),
        );
        (
            target,
            bind_expr,
            action_state,
            final_state,
            case_split_action,
        )
    }

    fn mk_naked_ite(then_branch: Expr, else_branch: Expr) -> Expr {
        // Deliberately ill-typed: zero universe levels on `ite`. Used by
        // the Wave 106 negative test to prove the kernel level-count
        // gate inside `close_goal` still fails-closed on this shape.
        Expr::apps(
            Expr::const_str("ite"),
            [
                state_t_ty(),
                Expr::const_str("cond"),
                Expr::const_str("instCond"),
                then_branch,
                else_branch,
            ],
        )
    }

    fn build_bind_case_split_fixture_with_naked_ite() -> (Expr, Expr, Expr, Expr, Expr) {
        let action = Expr::const_str("action");
        let action_run = mk_state_t_run(action.clone(), Expr::const_str("s"));
        let action_value = mk_prod_fst(action_run.clone());
        let action_state = mk_prod_snd(action_run);
        let continuation = Expr::lam(
            BinderInfo::Default,
            Expr::const_str("R"),
            mk_naked_ite(mk_pure(Expr::bvar(0)), mk_pure(Expr::bvar(0))),
        );
        let bind_expr = mk_bind(action, continuation);
        let bind_run = mk_state_t_run(bind_expr.clone(), Expr::const_str("s"));
        let final_state = mk_prod_snd(bind_run);
        let case_split_action = mk_naked_ite(mk_pure(action_value.clone()), mk_pure(action_value));
        let target = mk_eq(
            Expr::const_str("R"),
            mk_memory(final_state.clone()),
            mk_memory(Expr::const_str("s")),
        );
        (
            target,
            bind_expr,
            action_state,
            final_state,
            case_split_action,
        )
    }

    #[test]
    fn test_analyze_case_split_ite_detects() {
        let env = setup_state_t_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();
        let ite_expr = mk_ite(
            Expr::const_str("then_branch"),
            Expr::const_str("else_branch"),
        );

        assert!(matches!(
            analyze_case_split(&state, &goal, &ite_expr),
            Some(CaseSplitPattern::Ite { .. })
        ));
    }

    #[test]
    fn test_analyze_case_split_dite_detects() {
        // Closed in Wave 91: the analyzer now structurally recognises
        // `dite` even in a bare state where the kernel `Decidable`
        // predicate has not been initialised. The fix was a dispatch
        // ordering issue: `name_matches` uses `ends_with`, so "dite"
        // also satisfies the ITE suffix check, and the ITE arm was
        // shadowing the DITE arm. The DITE arm now runs first.
        let env = setup_state_t_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();
        let dite_expr = mk_dite(
            Expr::const_str("then_branch"),
            Expr::const_str("else_branch"),
        );

        assert!(
            matches!(
                analyze_case_split(&state, &goal, &dite_expr),
                Some(CaseSplitPattern::Dite { .. })
            ),
            "analyze_case_split must detect Dite in a bare state",
        );
    }

    #[test]
    fn test_analyze_case_split_ite_not_misclassified_as_dite() {
        // Negative guard for Wave 91: plain `ite` must NOT be
        // misclassified as `Dite`. Establishes that reordering the
        // dispatch did not collapse Ite -> Dite recognition.
        let env = setup_state_t_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();
        let ite_expr = mk_ite(
            Expr::const_str("then_branch"),
            Expr::const_str("else_branch"),
        );

        assert!(
            matches!(
                analyze_case_split(&state, &goal, &ite_expr),
                Some(CaseSplitPattern::Ite { .. })
            ),
            "plain `ite` must still classify as Ite, not Dite",
        );
    }

    #[test]
    fn test_analyze_case_split_except_cases_on_detects() {
        let env = setup_state_t_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();
        let except_expr = mk_except_cases_on(
            Expr::const_str("major"),
            Expr::const_str("error_branch"),
            Expr::const_str("ok_branch"),
        );

        assert!(matches!(
            analyze_case_split(&state, &goal, &except_expr),
            Some(CaseSplitPattern::ExceptCasesOn { .. })
        ));
    }

    #[test]
    fn test_find_chain_plan_bind_with_ite_terminal_decomposes() {
        let env = setup_state_t_env();
        let (target, _bind_expr, action_state, _final_state, case_split_action) =
            build_bind_case_split_fixture();
        let mut state = ProofState::new(env, target);
        let goal = state.current_goal().expect("goal").clone();
        let (_, lhs, rhs) = match_eq_expr(&state, &goal, &goal.target).expect("equality goal");
        let field = match_field_access(&lhs).expect("field access");

        let chain = find_chain_plan(&mut state, &goal, &lhs, &rhs, &field)
            .expect("chain should decompose through the bind + ite continuation");

        assert_eq!(chain.prefix_steps.len(), 1);
        assert_eq!(chain.prefix_steps[0].action, Expr::const_str("action"));
        assert_eq!(chain.prefix_steps[0].input_state, Expr::const_str("s"));
        assert_eq!(chain.prefix_steps[0].output_state, action_state.clone());

        match &chain.tail {
            ChainTail::CaseSplit(case_split) => {
                assert_eq!(case_split.split_expr, case_split_action);
                assert_eq!(case_split.branches.len(), 2);
                assert_eq!(case_split.branches[0].introduced_locals.len(), 1);
                assert_eq!(case_split.branches[1].introduced_locals.len(), 1);
            }
            ChainTail::Step(_) => panic!("expected a case-split tail"),
        }
    }

    #[test]
    fn test_monad_pres_bind_with_case_split_generates_step_goals() {
        let env = setup_state_t_env();
        let (target, _bind_expr, _action_state, _final_state, _case_split_action) =
            build_bind_case_split_fixture();
        let mut state = ProofState::new(env, target);

        // #38: the assembled `Or.rec`/`Classical.em` case-split proof term still
        // carries a universe-mismatched subterm — the `Or.rec` motive lambda's
        // body lands in `Sort(Succ Zero)` (`Type`) where the noConfusion
        // `Pi(cond, … , False)` context requires `Sort Zero` (`Prop`). Wave 106
        // fixed the `ite.{1}` head, but this second universe defect was only
        // hidden by the lenient (`infer_only=true`) close, which skips App-arg
        // sort checks. The kernel-strict close that `close_goal` now performs
        // rejects the term exactly as `Environment::add_decl` would (App-arg
        // `Sort(Zero)` vs `Sort(Succ Zero)`), so monad_pres correctly refuses to
        // emit the unsound proof. Repairing the motive's universe is tracked
        // separately; this test pins the soundness gate (no unsound close).
        let result = monad_pres(&mut state, &[Expr::const_str("memory")]);
        assert!(
            result.is_err(),
            "monad_pres must reject the universe-ill-typed Or.rec case-split \
             proof under kernel-strict close_goal, got: {result:?}"
        );
    }

    #[test]
    fn test_monad_pres_bind_with_case_split_rejects_naked_ite_const() {
        // Negative: a fixture that builds the `ite` head WITHOUT universe
        // levels must still be rejected at `close_goal` time — the gate
        // we restored in Wave 106 must not silently paper over a
        // legitimately ill-typed `ite` head. This pins the gate so the
        // fix can't be silently regressed by re-introducing
        // `Expr::const_str("ite")` (zero-level) into a fixture.
        let env = setup_state_t_env();
        let (target, _bind_expr, _action_state, _final_state, _case_split_action) =
            build_bind_case_split_fixture_with_naked_ite();
        let mut state = ProofState::new(env, target);

        let result = monad_pres(&mut state, &[Expr::const_str("memory")]);
        assert!(
            result.is_err(),
            "monad_pres must NOT close a goal built from a zero-level `ite` Const — the kernel level-count check is the safety gate"
        );
    }

    #[test]
    fn test_monad_pres_goal_not_equality_errors() {
        let env = setup_state_t_env();
        let mut state = ProofState::new(env, Expr::const_str("cond"));
        let result = monad_pres(&mut state, &[Expr::const_str("memory")]);

        assert!(matches!(
            result,
            Err(TacticError::InvalidTarget { ref detail, .. }) if detail == "goal is not an equality"
        ));
    }

    #[test]
    fn test_monad_pres_mismatched_fields_errors() {
        let mut env = setup_env();
        add_axiom(
            &mut env,
            "S.other",
            Expr::arrow(Expr::const_str("S"), Expr::const_str("R")),
        );

        let target = mk_eq(
            Expr::const_str("R"),
            Expr::app(Expr::const_str("S.memory"), Expr::const_str("s'")),
            Expr::app(Expr::const_str("S.other"), Expr::const_str("s")),
        );
        let mut state = ProofState::new(env, target);
        let result = monad_pres(&mut state, &[Expr::const_str("memory")]);

        assert!(matches!(
            result,
            Err(TacticError::InvalidTarget { ref detail, .. })
                if detail == "goal does not compare the same field on both sides"
        ));
    }

    #[test]
    fn test_monad_pres_field_not_selected_errors() {
        let env = setup_env();
        let lhs = Expr::app(Expr::const_str("S.memory"), Expr::const_str("s"));
        let target = mk_eq(Expr::const_str("R"), lhs.clone(), lhs);
        let mut state = ProofState::new(env, target);
        let result = monad_pres(&mut state, &[Expr::const_str("other")]);

        assert!(matches!(
            result,
            Err(TacticError::InvalidTarget { ref detail, .. })
                if detail == "goal field does not match the fields requested by monad_pres"
        ));
    }

    // ========================================================================
    // Monadic pattern recognition
    // ========================================================================

    #[test]
    fn test_analyze_monad_expr_get() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let get_expr = Expr::const_str("StateT.get");
        assert!(matches!(
            analyze_monad_expr(&state, &goal, &get_expr),
            Some(MonadPattern::Get)
        ));
    }

    #[test]
    fn test_analyze_monad_expr_set() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let set_expr = Expr::apps(
            Expr::const_str("StateT.set"),
            [Expr::const_str("S"), Expr::const_str("s'")],
        );
        let pattern = analyze_monad_expr(&state, &goal, &set_expr);
        assert!(matches!(pattern, Some(MonadPattern::Set { .. })));
        if let Some(MonadPattern::Set { new_state }) = pattern {
            assert_eq!(new_state, Expr::const_str("s'"));
        }
    }

    #[test]
    fn test_analyze_monad_expr_modify() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let modify_expr = Expr::apps(
            Expr::const_str("StateT.modify"),
            [Expr::const_str("S"), Expr::const_str("f")],
        );
        let pattern = analyze_monad_expr(&state, &goal, &modify_expr);
        assert!(matches!(pattern, Some(MonadPattern::Modify { .. })));
        if let Some(MonadPattern::Modify { modifier }) = pattern {
            assert_eq!(modifier, Expr::const_str("f"));
        }
    }

    #[test]
    fn test_analyze_monad_expr_state_t_pure_as_return() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let return_expr = Expr::apps(
            Expr::const_str("StateT.pure"),
            [Expr::const_str("R"), Expr::const_str("v")],
        );
        assert!(matches!(
            analyze_monad_expr(&state, &goal, &return_expr),
            Some(MonadPattern::Return { .. })
        ));
    }

    #[test]
    fn test_analyze_monad_expr_unrecognized_returns_none() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let unknown_expr = Expr::const_str("SomeUnknownFunction");
        assert!(analyze_monad_expr(&state, &goal, &unknown_expr).is_none());
    }

    #[test]
    fn test_analyze_monad_expr_bind_with_short_names() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        // Test "bind" (short name)
        let bind_expr = Expr::apps(
            Expr::const_str("bind"),
            [Expr::const_str("act"), Expr::const_str("cont")],
        );
        assert!(matches!(
            analyze_monad_expr(&state, &goal, &bind_expr),
            Some(MonadPattern::Bind { .. })
        ));
    }

    #[test]
    fn test_analyze_monad_expr_get_short_name() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let get_expr = Expr::const_str("get");
        assert!(matches!(
            analyze_monad_expr(&state, &goal, &get_expr),
            Some(MonadPattern::Get)
        ));
    }

    // ========================================================================
    // name_matches
    // ========================================================================

    #[test]
    fn test_name_matches_exact() {
        let name = Name::from_string("Bind.bind");
        assert!(name_matches(&name, BIND_NAMES));
    }

    #[test]
    fn test_name_matches_suffix() {
        // "Monad.Bind.bind" ends with "Bind.bind"
        let name = Name::from_string("Monad.Bind.bind");
        assert!(name_matches(&name, BIND_NAMES));
    }

    #[test]
    fn test_name_matches_no_match() {
        let name = Name::from_string("FooBar.baz");
        assert!(!name_matches(&name, BIND_NAMES));
    }

    // ========================================================================
    // FieldAccess
    // ========================================================================

    #[test]
    fn test_match_field_access_proj() {
        let base = Expr::const_str("s");
        let proj = Expr::proj(Name::from_string("MachineState"), 2, base);
        let access = match_field_access(&proj);
        assert!(access.is_some());
        let access = access.unwrap();
        assert!(matches!(access, FieldAccess::Proj { field_idx: 2, .. }));
        assert_eq!(access.base(), &Expr::const_str("s"));
    }

    #[test]
    fn test_match_field_access_app() {
        let expr = Expr::app(Expr::const_str("S.memory"), Expr::const_str("s"));
        let access = match_field_access(&expr);
        assert!(access.is_some());
        let access = access.unwrap();
        assert!(matches!(access, FieldAccess::App { .. }));
        assert_eq!(access.base(), &Expr::const_str("s"));
    }

    #[test]
    fn test_match_field_access_no_args_returns_none() {
        let expr = Expr::const_str("S.memory");
        let access = match_field_access(&expr);
        assert!(access.is_none());
    }

    #[test]
    fn test_field_access_same_field_proj() {
        let a = FieldAccess::Proj {
            struct_name: Name::from_string("S"),
            field_idx: 1,
            base: Expr::const_str("s"),
        };
        let b = FieldAccess::Proj {
            struct_name: Name::from_string("S"),
            field_idx: 1,
            base: Expr::const_str("s'"),
        };
        assert!(a.same_field(&b));
    }

    #[test]
    fn test_field_access_different_field_idx() {
        let a = FieldAccess::Proj {
            struct_name: Name::from_string("S"),
            field_idx: 1,
            base: Expr::const_str("s"),
        };
        let b = FieldAccess::Proj {
            struct_name: Name::from_string("S"),
            field_idx: 2,
            base: Expr::const_str("s'"),
        };
        assert!(!a.same_field(&b));
    }

    #[test]
    fn test_field_access_with_base() {
        let access = FieldAccess::App {
            head: Expr::const_str("S.memory"),
            prefix_args: vec![],
            base: Expr::const_str("s"),
        };
        let new_expr = access.with_base(Expr::const_str("s'"));
        // Should produce S.memory(s')
        assert_eq!(
            new_expr,
            Expr::app(Expr::const_str("S.memory"), Expr::const_str("s'"))
        );
    }

    #[test]
    fn test_field_access_with_base_proj() {
        let access = FieldAccess::Proj {
            struct_name: Name::from_string("MachineState"),
            field_idx: 2,
            base: Expr::const_str("s"),
        };
        let new_expr = access.with_base(Expr::const_str("s'"));
        assert_eq!(
            new_expr,
            Expr::proj(Name::from_string("MachineState"), 2, Expr::const_str("s'"))
        );
    }

    // ========================================================================
    // field_selected
    // ========================================================================

    #[test]
    fn test_field_selected_empty_list_matches_all() {
        let field = FieldAccess::App {
            head: Expr::const_str("S.memory"),
            prefix_args: vec![],
            base: Expr::const_str("s"),
        };
        assert!(field_selected(&field, &[]));
    }

    #[test]
    fn test_field_selected_matching_field() {
        let field = FieldAccess::App {
            head: Expr::const_str("S.memory"),
            prefix_args: vec![],
            base: Expr::const_str("s"),
        };
        assert!(field_selected(&field, &[Expr::const_str("memory")]));
    }

    #[test]
    fn test_field_selected_non_matching_field() {
        let field = FieldAccess::App {
            head: Expr::const_str("S.memory"),
            prefix_args: vec![],
            base: Expr::const_str("s"),
        };
        assert!(!field_selected(&field, &[Expr::const_str("permissions")]));
    }

    #[test]
    fn test_field_selected_multiple_candidates() {
        let field = FieldAccess::App {
            head: Expr::const_str("S.memory"),
            prefix_args: vec![],
            base: Expr::const_str("s"),
        };
        assert!(field_selected(
            &field,
            &[Expr::const_str("permissions"), Expr::const_str("memory")]
        ));
    }

    // ========================================================================
    // match_eq_expr
    // ========================================================================

    #[test]
    fn test_match_eq_expr_valid() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let eq = mk_eq(
            Expr::const_str("R"),
            Expr::const_str("a"),
            Expr::const_str("b"),
        );
        let result = match_eq_expr(&state, &goal, &eq);
        assert!(result.is_some());
        let (ty, lhs, rhs) = result.unwrap();
        assert_eq!(ty, Expr::const_str("R"));
        assert_eq!(lhs, Expr::const_str("a"));
        assert_eq!(rhs, Expr::const_str("b"));
    }

    #[test]
    fn test_match_eq_expr_non_eq_returns_none() {
        let env = setup_env();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().expect("goal").clone();

        let non_eq = Expr::const_str("NotEq");
        assert!(match_eq_expr(&state, &goal, &non_eq).is_none());
    }

    // ========================================================================
    // compose_preservation_proof
    // ========================================================================

    #[test]
    fn test_compose_single_step() {
        let alpha = Expr::const_str("R");
        let s0 = Expr::const_str("f0");
        let s1 = Expr::const_str("f1");
        let h01 = Expr::const_str("h01");

        let proof = compose_preservation_proof(alpha, &[s0, s1], std::slice::from_ref(&h01));
        // Single step: should just return the step proof directly
        assert_eq!(proof, h01);
    }

    #[test]
    fn test_compose_empty_steps() {
        let alpha = Expr::const_str("R");
        let s0 = Expr::const_str("f0");

        let proof = compose_preservation_proof(alpha.clone(), std::slice::from_ref(&s0), &[]);
        // No steps: should return Eq.refl
        assert_eq!(
            proof.get_app_fn(),
            &Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())])
        );
    }

    #[test]
    fn test_compose_three_step_chain() {
        let alpha = Expr::const_str("R");
        let s0 = Expr::const_str("f0");
        let s1 = Expr::const_str("f1");
        let s2 = Expr::const_str("f2");
        let s3 = Expr::const_str("f3");
        let h01 = Expr::const_str("h01");
        let h12 = Expr::const_str("h12");
        let h23 = Expr::const_str("h23");

        let proof = compose_preservation_proof(alpha.clone(), &[s0, s1, s2, s3], &[h01, h12, h23]);
        // Should produce nested Eq.trans calls
        assert_eq!(
            proof.get_app_fn(),
            &Expr::const_str_levels("Eq.trans", vec![Level::succ(Level::zero())])
        );
    }

    // ========================================================================
    // mk_eq helpers
    // ========================================================================

    #[test]
    fn test_mk_eq_structure() {
        let eq = mk_eq(
            Expr::const_str("Nat"),
            Expr::const_str("a"),
            Expr::const_str("b"),
        );
        let args: Vec<Expr> = eq.get_app_args().into_iter().cloned().collect();
        assert_eq!(
            eq.get_app_fn(),
            &Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())])
        );
        assert_eq!(args.len(), 3);
        assert_eq!(args[0], Expr::const_str("Nat"));
        assert_eq!(args[1], Expr::const_str("a"));
        assert_eq!(args[2], Expr::const_str("b"));
    }

    #[test]
    fn test_mk_eq_refl_structure() {
        let refl = mk_eq_refl(Expr::const_str("Nat"), Expr::const_str("x"));
        let args: Vec<Expr> = refl.get_app_args().into_iter().cloned().collect();
        assert_eq!(
            refl.get_app_fn(),
            &Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())])
        );
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], Expr::const_str("Nat"));
        assert_eq!(args[1], Expr::const_str("x"));
    }

    // ========================================================================
    // monad_pres tactic error cases
    // ========================================================================

    #[test]
    fn test_monad_pres_error_not_equality() {
        let env = setup_env();
        // Target is not an equality -- just a type
        let target = Expr::const_str("S");
        let mut state = ProofState::new(env, target);
        let result = monad_pres(&mut state, &[]);
        assert!(result.is_err());
        match result {
            Err(TacticError::InvalidTarget { tactic, detail }) => {
                assert_eq!(tactic, "monad_pres");
                assert!(detail.contains("not an equality"));
            }
            other => panic!("expected InvalidTarget, got {other:?}"),
        }
    }

    #[test]
    fn test_monad_pres_error_no_field_projection() {
        let env = setup_env();
        // lhs/rhs are plain constants, not field projections
        let target = mk_eq(
            Expr::const_str("R"),
            Expr::const_str("a"),
            Expr::const_str("b"),
        );
        let mut state = ProofState::new(env, target);
        let result = monad_pres(&mut state, &[]);
        assert!(result.is_err());
        match result {
            Err(TacticError::InvalidTarget { tactic, detail }) => {
                assert_eq!(tactic, "monad_pres");
                assert!(detail.contains("not a recognizable state field projection"));
            }
            other => panic!("expected InvalidTarget, got {other:?}"),
        }
    }

    #[test]
    fn test_monad_pres_error_mismatched_fields() {
        let env = setup_env();
        // Add a second field accessor
        let mut env2 = env;
        env2.add_decl(Declaration::Axiom {
            name: Name::from_string("S.permissions"),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str("S"), Expr::const_str("R")),
        })
        .expect("permissions field");

        let lhs = Expr::app(Expr::const_str("S.memory"), Expr::const_str("s'"));
        let rhs = Expr::app(Expr::const_str("S.permissions"), Expr::const_str("s"));
        let target = mk_eq(Expr::const_str("R"), lhs, rhs);

        let mut state = ProofState::new(env2, target);
        let result = monad_pres(&mut state, &[]);
        assert!(result.is_err());
        match result {
            Err(TacticError::InvalidTarget { tactic, detail }) => {
                assert_eq!(tactic, "monad_pres");
                assert!(detail.contains("same field"));
            }
            other => panic!("expected InvalidTarget about same field, got {other:?}"),
        }
    }

    #[test]
    fn test_monad_pres_error_field_not_selected() {
        let env = setup_env();
        let lhs = Expr::app(Expr::const_str("S.memory"), Expr::const_str("s"));
        let target = mk_eq(Expr::const_str("R"), lhs.clone(), lhs);

        let mut state = ProofState::new(env, target);
        // Request "permissions" but goal is about "memory"
        let result = monad_pres(&mut state, &[Expr::const_str("permissions")]);
        assert!(result.is_err());
        match result {
            Err(TacticError::InvalidTarget { tactic, detail }) => {
                assert_eq!(tactic, "monad_pres");
                assert!(detail.contains("does not match"));
            }
            other => panic!("expected InvalidTarget about field mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_monad_pres_refl_with_multi_arg_accessor() {
        // Test with a second field accessor to verify field matching works
        let mut env = setup_env();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("S.refCounts"),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str("S"), Expr::const_str("R")),
        })
        .expect("refCounts field");

        let lhs = Expr::app(Expr::const_str("S.refCounts"), Expr::const_str("s"));
        let target = mk_eq(Expr::const_str("R"), lhs.clone(), lhs);

        let mut state = ProofState::new(env, target);
        // Empty field_names means all fields match
        let result = monad_pres(&mut state, &[]);
        assert!(result.is_ok());
        assert!(state.is_complete());
    }

    // ========================================================================
    // name_tail
    // ========================================================================

    #[test]
    fn test_name_tail_dotted() {
        assert_eq!(name_tail("S.memory"), "memory");
    }

    #[test]
    fn test_name_tail_no_dot() {
        assert_eq!(name_tail("memory"), "memory");
    }

    #[test]
    fn test_name_tail_multiple_dots() {
        assert_eq!(name_tail("MachineState.fields.memory"), "memory");
    }

    // ========================================================================
    // chain_boundary_states — removed after ChainPlan struct refactor
    // (ChainPlan now uses prefix_steps + tail, not steps)
    // ========================================================================

    // ========================================================================
    // MonadPattern Debug display
    // ========================================================================

    #[test]
    fn test_monad_pattern_debug_format() {
        let pat = MonadPattern::Pure {
            value: Expr::const_str("v"),
        };
        let debug = format!("{pat:?}");
        assert!(debug.contains("Pure"));
    }

    #[test]
    fn test_monad_pattern_clone() {
        let pat = MonadPattern::Bind {
            action: Expr::const_str("act"),
            continuation: Expr::const_str("cont"),
        };
        let cloned = pat.clone();
        assert!(matches!(cloned, MonadPattern::Bind { .. }));
    }
}
