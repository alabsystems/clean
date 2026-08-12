// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition unfolding tactics
//!
//! Provides tactics for unfolding definitions in goals and hypotheses.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolder, ExprVisitor, LevelVec};

use super::{ProofState, TacticError, TacticResult};

// ============================================================================
// Definition Tactics
// ============================================================================

/// Specifies where an unfold operation should target.
#[derive(Debug, Clone, PartialEq, Eq)]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) enum UnfoldTarget {
    /// Unfold in the current goal target.
    Goal,
    /// Unfold in a named hypothesis.
    Hypothesis(String),
}

/// Unfold a definition in the goal.
///
/// Replaces occurrences of a constant with its definition.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `name` identifies a constant in the environment; on `Ok(())` that
///   constant has a definition and occurs in the current goal target.
/// ENSURES: On `Ok(())`, the current goal target is rewritten by substituting the
///   named constant with its definition.
/// ENSURES: On `Ok(())`, the goal stack shape and local context are unchanged;
///   only the current target is updated.
pub fn unfold(state: &mut ProofState, name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();

    // Try to find the definition in the environment
    let def_name = Name::from_string(name);
    let const_info = state
        .env
        .get_const(&def_name)
        .ok_or_else(|| TacticError::UnfoldFailed {
            name: name.to_string(),
            reason: "is not a constant".into(),
        })?;

    let def_level_params = const_info.level_params.clone();
    let def_val = const_info
        .value
        .as_ref()
        .ok_or_else(|| TacticError::UnfoldFailed {
            name: name.to_string(),
            reason: "has no definition (axiom?)".into(),
        })?
        .clone();

    // Substitute the definition for the constant in the target, instantiating
    // the definition's universe params from each occurrence's level args.
    let unfolded = substitute_const_levels(&target, &def_name, &def_level_params, &def_val);

    if unfolded == target {
        return Err(TacticError::UnfoldFailed {
            name: name.to_string(),
            reason: "does not appear in the goal".into(),
        });
    }

    // Part of #2477: use replace_target_def_eq instead of in-place mutation.
    // Definition unfolding is definitionally equal by construction.
    state.replace_target_def_eq(unfolded)
}

/// Test-only helper: substitute a constant with its definition in an
/// expression, ignoring the universe levels each occurrence carries.
///
/// Correct ONLY for a MONOMORPHIC definition (empty `level_params`). Every
/// production caller goes through [`substitute_const_levels`] instead, which
/// instantiates the definition's universe parameters (RC-E.2); this wrapper
/// survives purely so the structural-traversal tests (Proj / MData / Squash
/// recursion) can keep their terse three-argument form.
#[cfg(test)]
pub(crate) fn substitute_const(expr: &Expr, name: &Name, value: &Expr) -> Expr {
    substitute_const_levels(expr, name, &[], value)
}

/// Helper: substitute a constant with its definition in an expression,
/// instantiating the definition's universe parameters at each occurrence.
///
/// Uses `ExprFolder` for structural recursion over all ExprKind variants
/// (including Cubical and ZFC extensions). Part of #2092.
///
/// RC-E.2: `fold_const` used to DROP the `levels` of the node it replaced. A
/// universe-polymorphic definition's stored value is written over the
/// declaration's own level params, so substituting it verbatim for
/// `@MyId.{0} …` left a dangling `Sort (Param u)` behind — hence `unfold id at
/// hid` failing with `TypeMismatch { expected: Sort(Param(u)) }` under real
/// `Init`, while the monomorphic local-def spelling passed. Each occurrence
/// supplies its own level arguments, so the substitution has to instantiate the
/// body per occurrence, not once.
///
/// REQUIRES: `expr` is a well-formed expression tree; `value` is the stored
///   value of the declaration named `name`, whose universe parameters are
///   `def_level_params`.
/// ENSURES: Returns an expression where every `Const(name, levels)` node is
///   replaced with `value` under the substitution
///   `def_level_params[i] := levels[i]`.
/// ENSURES: A monomorphic definition (`def_level_params` empty) substitutes the
///   body unchanged, exactly as before.
/// ENSURES: Non-matching nodes preserve their constructor/metadata while
///   recursively rewriting children; recursion is stack-safe.
pub(crate) fn substitute_const_levels(
    expr: &Expr,
    name: &Name,
    def_level_params: &[Name],
    value: &Expr,
) -> Expr {
    struct SubstConstFolder<'a> {
        target_name: &'a Name,
        def_level_params: &'a [Name],
        replacement: &'a Expr,
    }

    impl ExprFolder for SubstConstFolder<'_> {
        fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
            if name == self.target_name {
                // `instantiate_level_params_direct` returns the body unchanged
                // when either slice is empty, and `zip`-truncates a length
                // mismatch rather than indexing out of bounds.
                self.replacement
                    .instantiate_level_params_direct(self.def_level_params, levels)
            } else {
                Expr::const_(name.clone(), levels.clone())
            }
        }
    }

    let mut folder = SubstConstFolder {
        target_name: name,
        def_level_params,
        replacement: value,
    };
    folder.fold_expr(expr)
}

/// Unfold a definition in a hypothesis.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, `def_name` identifies a constant with a definition and
///   `hyp_name` identifies a hypothesis in the current goal's local context.
/// ENSURES: On `Ok(())`, only the named hypothesis type is rewritten via
///   [`substitute_const`]; the goal target is unchanged.
/// ENSURES: Returns `Err(HypothesisNotFound)` when `hyp_name` is absent and
///   `Err(UnfoldFailed)` when the definition is missing, opaque, or absent from
///   the hypothesis type.
pub fn unfold_at(state: &mut ProofState, def_name: &str, hyp_name: &str) -> TacticResult {
    // First get the definition value from the environment
    let def_name_obj = Name::from_string(def_name);
    let const_info =
        state
            .env
            .get_const(&def_name_obj)
            .ok_or_else(|| TacticError::UnfoldFailed {
                name: def_name.to_string(),
                reason: "is not a constant".into(),
            })?;

    let def_level_params = const_info.level_params.clone();
    let def_val = const_info
        .value
        .as_ref()
        .ok_or_else(|| TacticError::UnfoldFailed {
            name: def_name.to_string(),
            reason: "has no definition (axiom?)".into(),
        })?
        .clone();

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis and route the defeq rewrite through the shared
    // proof-carry local replacement helper.
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .cloned()
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    let new_ty = substitute_const_levels(&hyp_decl.ty, &def_name_obj, &def_level_params, &def_val);

    if new_ty == hyp_decl.ty {
        return Err(TacticError::UnfoldFailed {
            name: def_name.to_string(),
            reason: format!("does not appear in hypothesis '{hyp_name}'"),
        });
    }

    state.replace_local_decl_def_eq(hyp_decl.fvar, new_ty)
}

/// Delta-reduce (unfold) all definitions in the goal.
///
/// This iteratively unfolds definitions until no more can be unfolded.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal target has undergone at least one
///   successful definition unfolding.
/// ENSURES: The tactic performs at most `MAX_ITERATIONS` scans and returns
///   `Err(NoProgress)` when the target is unchanged.
pub fn delta(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let original_target = goal.target.clone();

    let mut target = original_target.clone();
    let mut changed = true;
    let mut iterations = 0;
    const MAX_ITERATIONS: usize = 100;

    while changed && iterations < MAX_ITERATIONS {
        changed = false;
        iterations += 1;

        // Collect all constants in the expression
        let consts = collect_consts(&target);

        for const_name in consts {
            if let Some(const_info) = state.env.get_const(&const_name) {
                if let Some(def_val) = &const_info.value {
                    let new_target = substitute_const_levels(
                        &target,
                        &const_name,
                        &const_info.level_params,
                        def_val,
                    );
                    if new_target != target {
                        target = new_target;
                        changed = true;
                        break; // Restart scan after substitution
                    }
                }
            }
        }
    }

    if target == original_target {
        return Err(TacticError::NoProgress {
            tactic: "delta".into(),
        });
    }

    // Part of #2477: use replace_target_def_eq instead of in-place mutation.
    // Iterated definition unfolding is definitionally equal by construction.
    state.replace_target_def_eq(target)
}

/// Reduce the goal target to weak-head normal form.
///
/// This is the conv-mode reduction tactic (`conv => whnf`); used standalone it
/// reduces the current goal to its WHNF (beta/delta/iota/zeta head reduction via
/// the kernel). The result is definitionally equal to the target by
/// construction, so it is installed through [`ProofState::replace_target_def_eq`]
/// with no proof obligation.
///
/// It works inside `conv => …` for free: the compound `conv` handler runs its
/// body tactics through the generic evaluator on the focused sub-goal (see
/// `builtins_phase3d_conv::goal::eval_conv_goal`), then reconstructs and installs
/// the focus via the same definitional-equality fast path. Registering `whnf` as
/// an ordinary tactic therefore needs no conv-specific parser or dispatch.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal target equals `whnf(target)` (defeq to
///   the original); goal-stack shape and local context are unchanged.
/// ENSURES: Returns `Err(NoProgress)` when the target is already in WHNF.
pub fn whnf(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let reduced = state.whnf(&goal, &target);
    if reduced == target {
        return Err(TacticError::NoProgress {
            tactic: "whnf".into(),
        });
    }
    // WHNF is definitionally equal to the target by construction.
    state.replace_target_def_eq(reduced)
}

/// Reduce the goal target toward normal form (head reduction plus
/// argument-position redexes), via [`ProofState::normalize`].
///
/// Like [`whnf`] but also normalizes inside applications, so it makes progress on
/// goals such as `F ((fun x => x) a)` where `whnf` (head-only) cannot. The result
/// is definitionally equal, so it is installed through `replace_target_def_eq`
/// (no proof obligation) and works inside `conv => reduce` via the generic
/// conv-body evaluator, exactly like `whnf`.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the goal target equals `normalize(target)` (defeq).
/// ENSURES: Returns `Err(NoProgress)` when the target is already normal.
pub fn reduce(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let reduced = state.normalize(&goal, &target);
    if reduced == target {
        return Err(TacticError::NoProgress {
            tactic: "reduce".into(),
        });
    }
    state.replace_target_def_eq(reduced)
}

/// Helper: collect all constant names in an expression
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns each constant name appearing in `expr` at most once, in
///   first-discovery traversal order.
/// ENSURES: Non-constant nodes contribute names only through recursive descent
///   into their children.
pub(crate) fn collect_consts(expr: &Expr) -> Vec<Name> {
    struct ConstCollector<'a> {
        consts: &'a mut Vec<Name>,
    }

    impl ExprVisitor for ConstCollector<'_> {
        type Result = ();

        fn combine(&self, _a: (), _b: ()) {}

        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
            if !self.consts.contains(name) {
                self.consts.push(name.clone());
            }
        }
    }

    let mut consts = Vec::new();
    let mut visitor = ConstCollector {
        consts: &mut consts,
    };
    visitor.visit_expr(expr);
    consts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::ElabCtx;
    use crate::tactic::registry::TacticEval;
    use clean_kernel::{BinderInfo, Declaration, Environment};
    use clean_parser::{Span, SurfaceExpr, SurfaceTactic, SurfaceTacticLocation};

    #[test]
    fn test_reduce_normalizes_argument_position_redex() {
        // `F ((fun x : Nat => x) Nat.zero) : Prop` has a redex in *argument*
        // position — `whnf` (head-only) cannot touch it, but `reduce` normalizes
        // it to `F Nat.zero`.
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_true_false().unwrap();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let pred_ty = Expr::pi(BinderInfo::Default, nat.clone(), Expr::prop());
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("F"),
            level_params: vec![],
            type_: pred_ty,
        })
        .unwrap();

        let f = Expr::const_(Name::from_string("F"), vec![]);
        let id_app = Expr::app(
            Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
            zero.clone(),
        );
        let target = Expr::app(f.clone(), id_app);

        let mut state = ProofState::new(env, target);
        // `whnf` makes no progress (the redex is not at the head).
        assert!(
            matches!(whnf(&mut state), Err(TacticError::NoProgress { .. })),
            "whnf should not reduce an argument-position redex"
        );
        // `reduce` does.
        reduce(&mut state).expect("reduce should normalize the argument redex");
        assert_eq!(
            state.current_goal().expect("goal").target,
            Expr::app(f, zero),
            "F ((fun x => x) 0) reduces to F 0",
        );
    }

    #[test]
    fn test_conv_reduce_runs_inside_conv_block_end_to_end() {
        // `conv => reduce` through the REAL compound conv path (ElabCtx::eval →
        // eval_conv_goal → generic body evaluator → reduce on the focus → defeq
        // reconstruction). The focus has an argument-position redex that `whnf`
        // (head-only) cannot reach, so success specifically proves the defeq
        // reduction tactic runs inside conv mode via the generic evaluator.
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let pred_ty = Expr::pi(BinderInfo::Default, nat.clone(), Expr::prop());
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("F"),
            level_params: vec![],
            type_: pred_ty,
        })
        .unwrap();

        let f = Expr::const_(Name::from_string("F"), vec![]);
        let id_app = Expr::app(
            Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
            zero.clone(),
        );
        let goal = Expr::app(f.clone(), id_app); // F ((fun x => x) 0)
        let mut state = ProofState::new(env.clone(), goal);

        let mut ctx = ElabCtx::new(&env);
        ctx.eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "reduce".to_string(),
                    args: vec![],
                }],
            ),
        )
        .expect("`conv => reduce` should run through the compound handler");

        assert_eq!(
            state.current_goal().expect("goal remains").target,
            Expr::app(f, zero),
            "`conv => reduce` should reduce `F ((fun x => x) 0)` to `F 0`",
        );
    }

    #[test]
    fn test_conv_whnf_reduces_head_redex_end_to_end() {
        // Companion to the conv-reduce test: `conv => whnf` reduces a head-position
        // beta redex through the real compound conv path, confirming `whnf`
        // specifically runs inside conv mode (not only `reduce`).
        let mut env = Environment::new();
        env.init_true_false().unwrap();
        let true_ = Expr::const_(Name::from_string("True"), vec![]);
        // Goal: `(fun p : Prop => p) True`  →whnf→  `True`.
        let goal = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            true_.clone(),
        );
        let mut state = ProofState::new(env.clone(), goal);

        let mut ctx = ElabCtx::new(&env);
        ctx.eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "whnf".to_string(),
                    args: vec![],
                }],
            ),
        )
        .expect("`conv => whnf` should run through the compound handler");

        assert_eq!(
            state.current_goal().expect("goal remains").target,
            true_,
            "`conv => whnf` should reduce `(fun p => p) True` to `True`",
        );
    }

    #[test]
    fn test_conv_delta_unfolds_definition_end_to_end() {
        // Completes the conv defeq-reduction trilogy (whnf / reduce / delta)
        // validated end-to-end: `conv => delta` unfolds a definition in the focus.
        let mut env = Environment::new();
        env.init_true_false().unwrap();
        let true_ = Expr::const_(Name::from_string("True"), vec![]);
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Foo"),
            level_params: vec![],
            type_: Expr::prop(),
            value: true_.clone(),
            is_reducible: true,
        })
        .unwrap();
        let foo = Expr::const_(Name::from_string("Foo"), vec![]);
        let mut state = ProofState::new(env.clone(), foo);

        let mut ctx = ElabCtx::new(&env);
        ctx.eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "delta".to_string(),
                    args: vec![],
                }],
            ),
        )
        .expect("`conv => delta` should run through the compound handler");

        assert_eq!(
            state.current_goal().expect("goal remains").target,
            true_,
            "`conv => delta` should unfold `Foo` (:= True) to `True`",
        );
    }

    #[test]
    fn test_conv_change_to_defeq_term_end_to_end() {
        // `conv => change True` replaces a focus that is definitionally equal to
        // `True` with `True`, exercising the defeq goal-change tactic inside conv.
        let mut env = Environment::new();
        env.init_true_false().unwrap();
        let true_ = Expr::const_(Name::from_string("True"), vec![]);
        // Focus: `(fun p : Prop => p) True`  (defeq `True`).
        let goal = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            true_.clone(),
        );
        let mut state = ProofState::new(env.clone(), goal);

        let mut ctx = ElabCtx::new(&env);
        ctx.eval(
            &mut state,
            &SurfaceTactic::Conv(
                Span::dummy(),
                SurfaceTacticLocation::Goal,
                vec![SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "change".to_string(),
                    args: vec![SurfaceExpr::Ident(Span::dummy(), "True".to_string())],
                }],
            ),
        )
        .expect("`conv => change True` should run through the compound handler");

        assert_eq!(
            state.current_goal().expect("goal remains").target,
            true_,
            "`conv => change True` should set the focus to `True`",
        );
    }

    #[test]
    fn test_whnf_beta_reduces_goal() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_true_false().unwrap();

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let true_ = Expr::const_(Name::from_string("True"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        // Goal: `(fun _ : Nat => True) Nat.zero` — a beta redex; whnf → `True`.
        let redex = Expr::app(Expr::lam(BinderInfo::Default, nat, true_.clone()), zero);

        let mut state = ProofState::new(env, redex);
        whnf(&mut state).expect("whnf should beta-reduce the goal");
        let target = &state.current_goal().expect("goal remains").target;
        assert_eq!(
            *target, true_,
            "whnf should reduce `(fun _ => True) 0` to `True`"
        );
    }

    #[test]
    fn test_whnf_no_progress_on_whnf_goal() {
        let mut env = Environment::new();
        env.init_true_false().unwrap();
        let true_ = Expr::const_(Name::from_string("True"), vec![]);
        let mut state = ProofState::new(env, true_);
        let err = whnf(&mut state).unwrap_err();
        assert!(
            matches!(err, TacticError::NoProgress { .. }),
            "whnf on an already-WHNF goal should report NoProgress, got: {err:?}"
        );
    }
}
