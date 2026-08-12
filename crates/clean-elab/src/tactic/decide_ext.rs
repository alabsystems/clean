// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended `decide` support for compound propositions and Bool reflection.

use super::combinator::try_tactic_preserving_state;
use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::decide::eval_decide;
use super::decide_eq::{decidable_type_check, eval_to_nat};
use super::equality::match_equality;
use super::norm_num::{eval_int_expr, try_eval_comparison};
use super::{is_false, match_and, match_iff, match_not, match_or, omega};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};
use std::time::Instant;

#[derive(Debug, Clone)]
pub(crate) enum Decision {
    True(Expr),
    False(Expr),
}

/// Configuration for extended decide search.
#[derive(Debug, Clone)]
pub(crate) struct DecideExtConfig {
    /// Maximum wall-clock time in milliseconds (`0` disables the timeout).
    pub timeout_ms: u64,
    /// Maximum recursive depth for compound proposition splitting.
    pub max_depth: usize,
    /// Whether arithmetic leaves should try `mathverse`.
    pub use_mathverse: bool,
}

impl Default for DecideExtConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 250,
            max_depth: 16,
            use_mathverse: true,
        }
    }
}

/// REQUIRES: `prop` is a proposition. ENSURES: Returns the arrow-to-`False` encoding of `Not prop`.
fn make_not(prop: &Expr) -> Expr {
    Expr::arrow(
        prop.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

/// REQUIRES: `false_proof : False`. ENSURES: Returns `False.elim goal_ty false_proof`.
fn mk_false_elim(goal_ty: &Expr, false_proof: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            goal_ty.clone(),
        ),
        false_proof,
    )
}

/// REQUIRES: `binder_ty` is well-formed. ENSURES: Returns a lambda over a fresh temporary fvar.
fn mk_lambda<F>(state: &mut ProofState, binder_ty: &Expr, body_builder: F) -> Expr
where
    F: FnOnce(&mut ProofState, Expr) -> Expr,
{
    let fvar = state.fresh_fvar();
    let body = body_builder(state, Expr::fvar(fvar)).abstract_fvar(fvar);
    Expr::lam(BinderInfo::Default, binder_ty.clone(), body)
}

/// REQUIRES: `decidable_expr : Decidable p`. ENSURES: Returns a payload when WHNF exposes `isTrue`/`isFalse`.
fn extract_decision_from_decidable(
    state: &ProofState,
    goal: &Goal,
    decidable_expr: &Expr,
) -> Option<Decision> {
    let reduced = state.whnf(goal, decidable_expr);
    let args = reduced.get_app_args();
    let ExprKind::Const(name, _) = reduced.get_app_fn().kind() else {
        return None;
    };
    let payload = args.last().cloned()?.clone();
    match name.to_string().as_str() {
        "Decidable.isTrue" => Some(Decision::True(payload)),
        "Decidable.isFalse" => Some(Decision::False(payload)),
        _ => None,
    }
}

/// REQUIRES: `target` is well-formed in `goal.local_ctx`. ENSURES: Returns the proof assigned to the temporary subgoal.
fn prove_with_tactic<F>(state: &ProofState, goal: &Goal, target: Expr, tactic: F) -> Option<Expr>
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let mut trial = state.clone();
    let meta_id = trial.fresh_meta_in_context(target.clone(), &goal.local_ctx);
    trial.root_meta_id = meta_id;
    trial.goals.clear();
    trial.goals.push_front(Goal {
        meta_id,
        target,
        local_ctx: goal.local_ctx.clone(),
        tag: goal.tag.clone(),
    });
    trial.invalidate_tc_cache();
    tactic(&mut trial).ok()?;
    trial.metas().get_assignment(meta_id).cloned()
}

/// REQUIRES: `target` is a proposition. ENSURES: Returns `true` only for ground Nat/Int equalities or comparisons.
fn is_arithmetic_target(target: &Expr) -> bool {
    if try_eval_comparison(target).is_some() {
        return true;
    }
    if let Some(inner) = match_not(target) {
        return is_arithmetic_target(&inner);
    }
    if let Ok((_ty, lhs, rhs, _)) = match_equality(target) {
        return (eval_to_nat(&lhs).is_some() && eval_to_nat(&rhs).is_some())
            || (eval_int_expr(&lhs).is_some() && eval_int_expr(&rhs).is_some());
    }
    false
}

/// REQUIRES: `target` is the current proposition. ENSURES: Returns exact, negated, or reducible `Decidable target` evidence from context.
pub(crate) fn search_decidable_in_context(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
) -> Option<Decision> {
    let decidable_target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        target.clone(),
    );
    for decl in &goal.local_ctx {
        let decl_ty = state.metas.instantiate(&decl.ty);
        if state.is_def_eq(goal, &decl_ty, target) {
            return Some(Decision::True(Expr::fvar(decl.fvar)));
        }
        if is_false(&decl_ty) {
            return Some(Decision::True(mk_false_elim(target, Expr::fvar(decl.fvar))));
        }
        if let Some(inner) = match_not(&decl_ty) {
            if state.is_def_eq(goal, &inner, target) {
                return Some(Decision::False(Expr::fvar(decl.fvar)));
            }
        }
        if state.is_def_eq(goal, &decl_ty, &decidable_target) {
            let source = decl.value.clone().unwrap_or_else(|| Expr::fvar(decl.fvar));
            if let Some(decision) = extract_decision_from_decidable(state, goal, &source) {
                return Some(decision);
            }
        }
    }
    None
}

/// REQUIRES: `ty` is well-formed. ENSURES: Returns local or generated `DecidableEq ty` evidence when a `*.decEq`/instance hook exists.
pub(crate) fn generate_decidable_eq_instance(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
) -> Option<Expr> {
    let target = Expr::app(
        Expr::const_(Name::from_string("DecidableEq"), vec![]),
        ty.clone(),
    );
    for decl in &goal.local_ctx {
        if state.is_def_eq(goal, &state.metas.instantiate(&decl.ty), &target) {
            return Some(decl.value.clone().unwrap_or_else(|| Expr::fvar(decl.fvar)));
        }
    }
    let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
    let ExprKind::Const(head, _) = ty.get_app_fn().kind() else {
        return None;
    };
    let dec_eq_name = Name::from_string(&format!("{head}.decEq"));
    if state.env().get_const(&dec_eq_name).is_some() {
        return Some(Expr::app(
            Expr::const_(Name::from_string("DecidableEq.mk"), vec![]),
            Expr::apps(Expr::const_(dec_eq_name, vec![]), args),
        ));
    }
    for pattern in [
        format!("instDecidableEq{head}"),
        format!("inst{head}DecidableEq"),
    ] {
        let inst_name = Name::from_string(&pattern);
        if state.env().get_const(&inst_name).is_some() {
            return Some(Expr::apps(
                Expr::const_(inst_name, vec![]),
                ty.get_app_args().into_iter().cloned(),
            ));
        }
    }
    None
}

/// REQUIRES: `target` is a proposition. ENSURES: Returns a decision for Bool equalities, including `decide p = true/false`.
pub(crate) fn bool_reflection(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
) -> Option<Decision> {
    let Ok((ty, lhs, rhs, _)) = match_equality(target) else {
        return None;
    };
    if !state.is_def_eq(goal, &ty, &Expr::const_(Name::from_string("Bool"), vec![])) {
        return None;
    }
    let inst = generate_decidable_eq_instance(state, goal, &ty)?;
    extract_decision_from_decidable(
        state,
        goal,
        &Expr::apps(
            Expr::const_(Name::from_string("DecidableEq.decEq"), vec![]),
            [ty, inst, lhs, rhs],
        ),
    )
}

/// REQUIRES: `target` is a proposition. ENSURES: Returns a decision for equality goals when `BEq.beq` reduces and a DecidableEq bridge is available.
pub(crate) fn beq_to_decidable_eq(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
) -> Option<Decision> {
    let Ok((ty, lhs, rhs, _)) = match_equality(target) else {
        return None;
    };
    let beq_target = Expr::app(Expr::const_(Name::from_string("BEq"), vec![]), ty.clone());
    let mut beq_inst = None;
    for decl in &goal.local_ctx {
        if state.is_def_eq(goal, &state.metas.instantiate(&decl.ty), &beq_target) {
            beq_inst = Some(decl.value.clone().unwrap_or_else(|| Expr::fvar(decl.fvar)));
            break;
        }
    }
    if beq_inst.is_none() {
        let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
        if let ExprKind::Const(head, _) = ty.get_app_fn().kind() {
            for pattern in [format!("instBEq{head}"), format!("inst{head}BEq")] {
                let inst_name = Name::from_string(&pattern);
                if state.env().get_const(&inst_name).is_some() {
                    beq_inst = Some(Expr::apps(Expr::const_(inst_name, vec![]), args.clone()));
                    break;
                }
            }
            if beq_inst.is_none() {
                let beq_name = Name::from_string(&format!("{head}.beq"));
                if state.env().get_const(&beq_name).is_some() {
                    beq_inst = Some(Expr::app(
                        Expr::const_(Name::from_string("BEq.mk"), vec![]),
                        Expr::apps(Expr::const_(beq_name, vec![]), args),
                    ));
                }
            }
        }
    }
    let beq_inst = beq_inst?;
    let beq_expr = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![]),
        [ty.clone(), beq_inst, lhs.clone(), rhs.clone()],
    );
    let reduced = state.whnf(goal, &beq_expr);
    let is_bool_lit = matches!(reduced.kind(), ExprKind::Const(name, _) if {
        let s = name.to_string();
        s == "Bool.true" || s == "Bool.false"
    });
    if !is_bool_lit {
        return None;
    }
    bool_reflection(state, goal, target)
}

/// REQUIRES: `target` is a proposition. ENSURES: Returns a synthesized `Decidable target` for And/Or/Not/Iff when recursive leaves can be decided within `config`.
pub(crate) fn synthesize_compound_decidable(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    config: &DecideExtConfig,
    started: Instant,
    depth: usize,
) -> Result<Option<Expr>, TacticError> {
    /// REQUIRES: `target` is a proposition. ENSURES: Returns direct proof or refutation evidence for recursive subgoals within `config`.
    fn resolve(
        state: &mut ProofState,
        goal: &Goal,
        target: &Expr,
        config: &DecideExtConfig,
        started: Instant,
        depth: usize,
    ) -> Result<Option<Decision>, TacticError> {
        if depth > config.max_depth {
            return Err(TacticError::DepthExceeded {
                tactic: "decide_ext".into(),
                max_depth: config.max_depth,
            });
        }
        if config.timeout_ms > 0 && started.elapsed().as_millis() > u128::from(config.timeout_ms) {
            return Err(TacticError::Timeout {
                detail: format!("decide_ext exceeded {}ms", config.timeout_ms),
            });
        }
        if let Some(decision) = search_decidable_in_context(state, goal, target) {
            return Ok(Some(decision));
        }
        if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
            return Ok(Some(Decision::True(Expr::const_(
                Name::from_string("True.intro"),
                vec![],
            ))));
        }
        if is_false(target) {
            return Ok(Some(Decision::False(mk_lambda(state, target, |_, h| h))));
        }
        if let Some((lhs, rhs)) = match_and(target) {
            let l = resolve(state, goal, &lhs, config, started, depth + 1)?;
            let r = resolve(state, goal, &rhs, config, started, depth + 1)?;
            return Ok(match (l, r) {
                (Some(Decision::True(lp)), Some(Decision::True(rp))) => {
                    Some(Decision::True(Expr::apps(
                        Expr::const_(Name::from_string("And.intro"), vec![]),
                        [lhs, rhs, lp, rp],
                    )))
                }
                (Some(Decision::False(ln)), _) => {
                    Some(Decision::False(mk_lambda(state, target, |_, h| {
                        Expr::app(
                            ln,
                            Expr::apps(
                                Expr::const_(Name::from_string("And.left"), vec![]),
                                [lhs, rhs, h],
                            ),
                        )
                    })))
                }
                (_, Some(Decision::False(rn))) => {
                    Some(Decision::False(mk_lambda(state, target, |_, h| {
                        Expr::app(
                            rn,
                            Expr::apps(
                                Expr::const_(Name::from_string("And.right"), vec![]),
                                [lhs, rhs, h],
                            ),
                        )
                    })))
                }
                _ => None,
            });
        }
        if let Some((lhs, rhs)) = match_or(target) {
            let l = resolve(state, goal, &lhs, config, started, depth + 1)?;
            let r = resolve(state, goal, &rhs, config, started, depth + 1)?;
            return Ok(match (l, r) {
                (Some(Decision::True(lp)), _) => Some(Decision::True(Expr::apps(
                    Expr::const_(Name::from_string("Or.inl"), vec![]),
                    [lhs, rhs, lp],
                ))),
                (_, Some(Decision::True(rp))) => Some(Decision::True(Expr::apps(
                    Expr::const_(Name::from_string("Or.inr"), vec![]),
                    [lhs, rhs, rp],
                ))),
                (Some(Decision::False(ln)), Some(Decision::False(rn))) => {
                    Some(Decision::False(mk_lambda(state, target, |state, h| {
                        let left = mk_lambda(state, &lhs, |_, hp| Expr::app(ln, hp));
                        let right = mk_lambda(state, &rhs, |_, hp| Expr::app(rn, hp));
                        Expr::apps(
                            Expr::const_(Name::from_string("Or.rec"), vec![]),
                            [
                                lhs,
                                rhs,
                                Expr::lam(
                                    BinderInfo::Default,
                                    target.clone(),
                                    Expr::const_(Name::from_string("False"), vec![]).lift(1),
                                ),
                                left,
                                right,
                                h,
                            ],
                        )
                    })))
                }
                _ => None,
            });
        }
        if let Some(inner) = match_not(target) {
            return Ok(
                match resolve(state, goal, &inner, config, started, depth + 1)? {
                    Some(Decision::True(pf)) => {
                        Some(Decision::False(mk_lambda(state, target, |_, h| {
                            Expr::app(h, pf)
                        })))
                    }
                    Some(Decision::False(np)) => Some(Decision::True(np)),
                    None => None,
                },
            );
        }
        if let Some((lhs, rhs)) = match_iff(target) {
            let l = resolve(state, goal, &lhs, config, started, depth + 1)?;
            let r = resolve(state, goal, &rhs, config, started, depth + 1)?;
            return Ok(match (l, r) {
                (Some(Decision::True(lp)), Some(Decision::True(rp))) => {
                    let fwd = mk_lambda(state, &lhs, |_, _| rp.clone());
                    let bwd = mk_lambda(state, &rhs, |_, _| lp.clone());
                    Some(Decision::True(Expr::apps(
                        Expr::const_(Name::from_string("Iff.intro"), vec![]),
                        [lhs, rhs, fwd, bwd],
                    )))
                }
                (Some(Decision::False(ln)), Some(Decision::False(rn))) => {
                    let fwd = mk_lambda(state, &lhs, |_, hp| {
                        mk_false_elim(&rhs, Expr::app(ln.clone(), hp))
                    });
                    let bwd = mk_lambda(state, &rhs, |_, hp| {
                        mk_false_elim(&lhs, Expr::app(rn.clone(), hp))
                    });
                    Some(Decision::True(Expr::apps(
                        Expr::const_(Name::from_string("Iff.intro"), vec![]),
                        [lhs, rhs, fwd, bwd],
                    )))
                }
                (Some(Decision::True(lp)), Some(Decision::False(rn))) => {
                    Some(Decision::False(mk_lambda(state, target, |_, h| {
                        let mp = Expr::apps(
                            Expr::const_(Name::from_string("Iff.mp"), vec![]),
                            [lhs, rhs, h, lp],
                        );
                        Expr::app(rn, mp)
                    })))
                }
                (Some(Decision::False(ln)), Some(Decision::True(rp))) => {
                    Some(Decision::False(mk_lambda(state, target, |_, h| {
                        let mpr = Expr::apps(
                            Expr::const_(Name::from_string("Iff.mpr"), vec![]),
                            [lhs, rhs, h, rp],
                        );
                        Expr::app(ln, mpr)
                    })))
                }
                _ => None,
            });
        }
        if let Some(decision) = bool_reflection(state, goal, target) {
            return Ok(Some(decision));
        }
        if let Some(decision) = beq_to_decidable_eq(state, goal, target) {
            return Ok(Some(decision));
        }
        if let Ok((ty, lhs, rhs, _)) = match_equality(target) {
            if state.is_def_eq(goal, &lhs, &rhs) {
                // Wave 94: Gap 4. `Eq.refl` is universe-polymorphic with
                // 1 level; infer it from the equality type before
                // emitting the proof term. Empty `vec![]` caused
                // `LevelCountMismatch` for `42 = 42 : Nat`.
                let level = super::conv_proof::infer_sort_level(
                    state,
                    goal,
                    &ty,
                    "decide_ext: refl level",
                )?;
                return Ok(Some(Decision::True(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq.refl"), vec![level]),
                        ty.clone(),
                    ),
                    lhs,
                ))));
            }
            if decidable_type_check(&ty)
                || generate_decidable_eq_instance(state, goal, &ty).is_some()
            {
                let dec = if let ExprKind::Const(head, _) = ty.get_app_fn().kind() {
                    let direct = Name::from_string(&format!("{head}.decEq"));
                    if state.env().get_const(&direct).is_some() {
                        Some(Expr::apps(
                            Expr::const_(direct, vec![]),
                            ty.get_app_args()
                                .into_iter()
                                .cloned()
                                .chain([lhs.clone(), rhs.clone()]),
                        ))
                    } else {
                        generate_decidable_eq_instance(state, goal, &ty).map(|inst| {
                            Expr::apps(
                                Expr::const_(Name::from_string("DecidableEq.decEq"), vec![]),
                                [ty, inst, lhs, rhs],
                            )
                        })
                    }
                } else {
                    None
                };
                if let Some(decidable) = dec {
                    if let Some(decision) = extract_decision_from_decidable(state, goal, &decidable)
                    {
                        return Ok(Some(decision));
                    }
                }
            }
        }
        if let Some(proof) = prove_with_tactic(state, goal, target.clone(), eval_decide) {
            return Ok(Some(Decision::True(proof)));
        }
        if config.use_mathverse && is_arithmetic_target(target) {
            if let Some(proof) = prove_with_tactic(state, goal, target.clone(), omega) {
                return Ok(Some(Decision::True(proof)));
            }
        }
        let not_target = make_not(target);
        if let Some(proof) = prove_with_tactic(state, goal, not_target.clone(), eval_decide) {
            return Ok(Some(Decision::False(proof)));
        }
        if config.use_mathverse && is_arithmetic_target(target) {
            if let Some(proof) = prove_with_tactic(state, goal, not_target, omega) {
                return Ok(Some(Decision::False(proof)));
            }
        }
        Ok(None)
    }

    Ok(
        resolve(state, goal, target, config, started, depth)?.map(|d| match d {
            Decision::True(proof) => Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                    target.clone(),
                ),
                proof,
            ),
            Decision::False(proof) => Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                    target.clone(),
                ),
                proof,
            ),
        }),
    )
}

/// REQUIRES: `state.goals` is non-empty. ENSURES: Closes the current goal with `mathverse` when it is a ground Nat/Int arithmetic proposition.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) fn try_mathverse_decide(
    state: &mut ProofState,
    config: &DecideExtConfig,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    if !config.use_mathverse || !is_arithmetic_target(&target) {
        return Err(TacticError::GoalMismatch(
            "decide_ext: goal is not a supported arithmetic proposition".into(),
        ));
    }
    if try_tactic_preserving_state(state, omega) {
        return Ok(());
    }
    Err(TacticError::ArithmeticFailed {
        tactic: "decide_ext".into(),
        reason: "mathverse could not close the goal".into(),
    })
}

/// REQUIRES: `target` is `@Eq Bool e Bool.true` or `@Eq Bool Bool.true e`. ENSURES: Returns the inner `e` when the pattern matches.
pub(crate) fn match_bool_eq_true(target: &Expr) -> Option<Expr> {
    let Ok((ty, lhs, rhs, _)) = match_equality(target) else {
        return None;
    };
    let is_bool = matches!(ty.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Bool"));
    if !is_bool {
        return None;
    }
    let is_true = |e: &Expr| matches!(e.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Bool.true"));
    if is_true(&rhs) {
        return Some(lhs);
    }
    if is_true(&lhs) {
        return Some(rhs);
    }
    None
}

/// REQUIRES: `target` is `@Eq Bool (BEq.beq ty inst a b) Bool.true` (or symmetric). ENSURES: Returns `(ty, a, b)`.
pub(crate) fn match_beq_eq_true(target: &Expr) -> Option<(Expr, Expr, Expr)> {
    let inner = match_bool_eq_true(target)?;
    let args = inner.get_app_args();
    let ExprKind::Const(name, _) = inner.get_app_fn().kind() else {
        return None;
    };
    if name != &Name::from_string("BEq.beq") || args.len() < 4 {
        return None;
    }
    Some((args[0].clone(), args[2].clone(), args[3].clone()))
}

/// REQUIRES: `ty` is a type constant. ENSURES: Returns the `DecidableEq` instance name when `ty.decEq` exists in the environment.
pub(crate) fn find_decidable_eq_instance(state: &ProofState, ty: &Expr) -> Option<Name> {
    let ExprKind::Const(head, _) = ty.get_app_fn().kind() else {
        return None;
    };
    let dec_eq_name = Name::from_string(&format!("{head}.decEq"));
    if state.env().get_const(&dec_eq_name).is_some() {
        return Some(dec_eq_name);
    }
    for pattern in [
        format!("instDecidableEq{head}"),
        format!("inst{head}DecidableEq"),
    ] {
        let inst_name = Name::from_string(&pattern);
        if state.env().get_const(&inst_name).is_some() {
            return Some(inst_name);
        }
    }
    None
}

/// REQUIRES: `state.goals` is non-empty. ENSURES: Like `eval_decide_ext` but with explicit configuration.
pub(crate) fn eval_decide_ext_with_config(
    state: &mut ProofState,
    config: &DecideExtConfig,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    if config.use_mathverse
        && is_arithmetic_target(&target)
        && try_tactic_preserving_state(state, omega)
    {
        return Ok(());
    }
    if let Some(Decision::True(proof)) = search_decidable_in_context(state, &goal, &target) {
        return state.close_goal(&goal, proof);
    }
    if let Some(Decision::True(proof)) = bool_reflection(state, &goal, &target) {
        return state.close_goal(&goal, proof);
    }
    if let Some(Decision::True(proof)) = beq_to_decidable_eq(state, &goal, &target) {
        return state.close_goal(&goal, proof);
    }
    if let Some(decidable) =
        synthesize_compound_decidable(state, &goal, &target, config, Instant::now(), 0)?
    {
        match extract_decision_from_decidable(state, &goal, &decidable) {
            Some(Decision::True(proof)) => return state.close_goal(&goal, proof),
            Some(Decision::False(_)) => {
                return Err(TacticError::InvalidTarget {
                    tactic: "decide_ext".into(),
                    detail: "proposition evaluates to false".into(),
                })
            }
            None => {}
        }
    }
    eval_decide(state)
}

/// REQUIRES: `state.goals` is non-empty. ENSURES: Closes the current goal using context search, compound synthesis, Bool reflection, BEq/DecidableEq bridging, or `mathverse`.
pub(crate) fn eval_decide_ext(state: &mut ProofState) -> TacticResult {
    let mut config = DecideExtConfig::default();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    let timeout_ms = state.options().timeout_ms();
    if timeout_ms > 0 {
        config.timeout_ms = timeout_ms;
    }
    eval_decide_ext_with_config(state, &config)
}
