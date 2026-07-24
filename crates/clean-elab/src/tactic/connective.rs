// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Logic connective tactics: split, left, right, exfalso, contradiction, by_contra.
//!
//! These tactics work with logical connectives (And, Or, Iff, False, Not).

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};

// =============================================================================
// Connective tactics: split, left, right
// =============================================================================

/// Split a conjunction goal into two subgoals and build `And.intro`.
///
/// For a goal `And A B`, produces subgoals `A` and `B` (left first) and
/// closes the current goal with `And.intro A B ?left ?right`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target WHNF-reduces to `And A B` or `Iff A B`
/// ENSURES: On Ok, original goal is closed with `And.intro`/`Iff.intro` proof
/// ENSURES: On Ok, two new subgoals are pushed (left first, then right)
/// ENSURES: On Err(GoalMismatch), goal head is not `And` or `Iff`; state unchanged
pub fn split_(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let target = state.whnf(&goal, &goal.target);
    let head = target.get_app_fn().clone();
    let args: Vec<Expr> = target.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, levels) if *name == Name::from_string("And") => {
            if args.len() != 2 {
                return Err(TacticError::GoalMismatch(
                    "split requires goal of form And a b".to_string(),
                ));
            }

            let left_ty = state.metas.instantiate(&args[0]);
            let right_ty = state.metas.instantiate(&args[1]);

            let left_meta_id = state.fresh_meta(left_ty.clone());
            let right_meta_id = state.fresh_meta(right_ty.clone());

            let left_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(left_meta_id)));
            let right_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(right_meta_id)));

            // Build And.intro a b ?left ?right
            let mut proof = Expr::const_(Name::from_string("And.intro"), levels.clone());
            proof = Expr::app(proof, args[0].clone());
            proof = Expr::app(proof, args[1].clone());
            proof = Expr::app(proof, left_meta.clone());
            proof = Expr::app(proof, right_meta.clone());

            // Part of #2154: type-check And.intro proof before accepting
            state.close_goal(&goal, proof)?;

            // Insert subgoals: left first, then right. Tag them with
            // `And.intro`'s field names (`left`, `right`) so `case left =>` /
            // `case right =>` can focus them, matching Lean 4's `constructor`.
            // Tags are focus metadata only; the kernel-checked proof term is
            // unchanged.
            let left_goal = Goal {
                meta_id: left_meta_id,
                target: left_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: Some("left".into()),
            };
            let right_goal = Goal {
                meta_id: right_meta_id,
                target: right_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: Some("right".into()),
            };

            state.goals.push_front(right_goal);
            state.goals.push_front(left_goal);
            Ok(())
        }
        ExprKind::Const(name, levels) if *name == Name::from_string("Iff") => {
            // Iff P Q splits into two implications: P → Q and Q → P
            if args.len() != 2 {
                return Err(TacticError::GoalMismatch(
                    "split requires goal of form Iff a b".to_string(),
                ));
            }

            let p = state.metas.instantiate(&args[0]);
            let q = state.metas.instantiate(&args[1]);

            // Goals: P → Q and Q → P
            let mp_ty = Expr::arrow(p.clone(), q.clone()); // mp: P → Q
            let mpr_ty = Expr::arrow(q.clone(), p.clone()); // mpr: Q → P

            let mp_meta_id = state.fresh_meta(mp_ty.clone());
            let mpr_meta_id = state.fresh_meta(mpr_ty.clone());

            let mp_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(mp_meta_id)));
            let mpr_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(mpr_meta_id)));

            // Build Iff.intro P Q ?mp ?mpr
            let mut proof = Expr::const_(Name::from_string("Iff.intro"), levels.clone());
            proof = Expr::app(proof, p.clone());
            proof = Expr::app(proof, q.clone());
            proof = Expr::app(proof, mp_meta.clone());
            proof = Expr::app(proof, mpr_meta.clone());

            // Part of #2154: type-check Iff.intro proof before accepting
            state.close_goal(&goal, proof)?;

            // Insert subgoals: mp first (P → Q), then mpr (Q → P). Tag them
            // with `Iff.intro`'s field names (`mp`, `mpr`) so `case mp =>` /
            // `case mpr =>` can focus them, matching Lean 4's `constructor`.
            // Tags are focus metadata only; the kernel-checked proof term is
            // unchanged.
            let mp_goal = Goal {
                meta_id: mp_meta_id,
                target: mp_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: Some("mp".into()),
            };
            let mpr_goal = Goal {
                meta_id: mpr_meta_id,
                target: mpr_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: Some("mpr".into()),
            };

            state.goals.push_front(mpr_goal);
            state.goals.push_front(mp_goal);
            Ok(())
        }
        // Fallback: not an `And`/`Iff` goal head. Lean's `split` also
        // case-splits a goal that CONTAINS an `if c then a else b` on the
        // condition's `Decidable` instance. Search for the first `ite` and, if
        // found, split on its instance via `Decidable.casesOn`. If there is no
        // `ite` either, fail closed.
        _ => split_ite(state, &goal),
    }
}

/// Split a goal that CONTAINS an `if c then a else b` on the condition's
/// `Decidable` instance, mirroring Lean 4's `split`.
///
/// Locates the first `@ite.{u} α c inst a b` subterm in `target` (the goal's
/// already-WHNF'd target) and closes the goal with
/// `@Decidable.casesOn.{0} c motive inst false_branch true_branch`, where
/// `motive := fun (w : Decidable c) => target[ite.inst := w]`. The two minor
/// premises become fresh metavariable subgoals whose targets are the
/// definitionally-reduced forms:
/// - `isFalse (h : ¬c)` branch → `target[ite := b]`, with `h : ¬c` in context
/// - `isTrue  (h : c)`  branch → `target[ite := a]`, with `h : c`  in context
///
/// (Lean's `Decidable` declares `isFalse` as constructor 0 and `isTrue` as
/// constructor 1, so `casesOn`'s minor premises are false-then-true; the `ite`
/// definition is `Decidable.casesOn c … inst false_case true_case`, so
/// `@ite α c (isTrue h) a b` ι-reduces to `a` and `… (isFalse h) …` to `b`.)
///
/// # Soundness
///
/// The assembled `Decidable.casesOn` term is kernel-rechecked by `close_goal`
/// against the original goal target (`motive inst ≡ target` definitionally, so
/// the check confirms the whole spine). Each branch's reduced target is
/// def-eq to `motive (isTrue/isFalse h)`, so the subgoal metas are re-verified
/// when solved. Zero domain-specific axioms: only `ite` / `Decidable`
/// (+ `.casesOn`) / `False` are referenced.
///
/// # Contract
///
/// ENSURES: On Ok, the goal is closed with a kernel-checked `Decidable.casesOn`
///   term and two subgoals are pushed (false/`¬c` case first, true/`c` second)
/// ENSURES: On Err(GoalMismatch), no `ite` was found; state unchanged
/// ENSURES: On Err(EnvironmentMissing), `Decidable.casesOn` is not registered
fn split_ite(state: &mut ProofState, goal: &Goal) -> TacticResult {
    // The target as the goal actually carries it (metas resolved). We search
    // for the `ite` here rather than in the WHNF'd target: WHNF delta-unfolds a
    // TOP-LEVEL `ite` (it is `is_reducible`) into its `Decidable.casesOn` body,
    // which would hide the very `ite` we need (e.g. the whole goal being
    // `if n = 0 then True else True`). The raw instantiated target keeps `ite`
    // intact whether it is the head (Prop goal) or nested (e.g. inside `Eq`).
    let target = state.metas.instantiate(&goal.target);

    // Find the first `@ite.{u} α c inst a b` subterm in the target. If there is
    // no `ite` (and the head was not `And`/`Iff`), this is the terminal
    // `split` mismatch — report it directly so the error is independent of
    // which auxiliary constants happen to be registered.
    let Some(ite) = find_first_ite(&target) else {
        return Err(TacticError::GoalMismatch(
            "split requires goal of form And a b, Iff a b, or one containing an if-then-else"
                .to_string(),
        ));
    };

    // An `ite` is present: `Decidable.casesOn` must be registered to split on
    // its instance (it is auto-generated with the `Decidable` inductive; the
    // whole prelude has it). Fail closed otherwise.
    let cases_on_name = Name::from_string("Decidable.casesOn");
    if state.env.get_const(&cases_on_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Decidable.casesOn".to_string(),
        });
    }

    // Rebuild the ite subterm as it actually appears in the (instantiated)
    // target, so `replace_expr` matches structurally.
    let ite_subterm = ite.rebuild();

    // Placeholder fvar standing for the abstracted `Decidable c` instance in
    // the motive. `abstract_fvar` turns it into `BVar(0)` under the motive's
    // binder; it never escapes into a subgoal (the reduced targets below do not
    // mention it).
    let hole_fvar = state.fresh_fvar();
    let hole = Expr::fvar(hole_fvar);

    // motive body = target with the ite's instance replaced by the hole fvar.
    let ite_hole = ite.with_inst(hole.clone());
    let motive_body = super::replace_expr(&target, &ite_subterm, &ite_hole);
    // motive = fun (w : Decidable c) => target[ite.inst := w]
    let decidable_c = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        ite.cond.clone(),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        decidable_c.clone(),
        motive_body.abstract_fvar(hole_fvar),
    );

    // Reduced branch targets (def-eq to `motive (isTrue/isFalse h)`):
    //   true  branch → target with ite replaced by its `then` value `a`
    //   false branch → target with ite replaced by its `else` value `b`
    let true_target = super::replace_expr(&target, &ite_subterm, &ite.then_val);
    let false_target = super::replace_expr(&target, &ite_subterm, &ite.else_val);

    // Hypothesis fvar for `h : c` / `h : ¬c`. The two branch lambdas are
    // PARALLEL binders, each its own `fun h => ?meta` directly under
    // `Decidable.casesOn`, both at binder depth 1 — so, exactly as in
    // `by_cases`, they can share ONE fvar id numbered from the goal's tactic
    // base without violating `close_fvars`' `(n - base) < depth` invariant.
    let h_fvar = FVarId::new(state.goal_fvar_base(goal));

    // ¬c = c → False (matches `Decidable.isFalse`'s argument type).
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let neg_c = Expr::pi(BinderInfo::Default, ite.cond.clone(), false_const);

    // Branch contexts: `h : ¬c` (false) and `h : c` (true).
    let mut false_ctx = goal.local_ctx.clone();
    false_ctx.push(LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: neg_c.clone(),
        value: None,
    });
    let mut true_ctx = goal.local_ctx.clone();
    true_ctx.push(LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: ite.cond.clone(),
        value: None,
    });

    // Fresh metavariables for the two branch subgoals, each stamped with its
    // own hypothesis context.
    let false_meta = state.fresh_meta_in_context(false_target.clone(), &false_ctx);
    let true_meta = state.fresh_meta_in_context(true_target.clone(), &true_ctx);

    // Branch lambdas: `fun (h : ¬c) => ?false_meta` and `fun (h : c) => ?true_meta`.
    let false_branch = Expr::lam(
        BinderInfo::Default,
        neg_c,
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(false_meta))).abstract_fvar(h_fvar),
    );
    let true_branch = Expr::lam(
        BinderInfo::Default,
        ite.cond.clone(),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(true_meta))).abstract_fvar(h_fvar),
    );

    // @Decidable.casesOn.{0} c motive inst false_branch true_branch
    // Motive returns the goal target (a Prop = Sort 0), so the eliminated sort
    // is `Sort 0` and `Decidable.casesOn` is instantiated at level 0.
    let cases_on = Expr::const_(cases_on_name, vec![Level::zero()]);
    let proof = Expr::apps(
        cases_on,
        [
            ite.cond.clone(),
            motive,
            ite.inst.clone(),
            false_branch,
            true_branch,
        ],
    );

    // Kernel-recheck the assembled Decidable.casesOn term against the goal.
    state.close_goal(goal, proof)?;

    // Push subgoals: false/`¬c` case first (so `isTrue`/`c` case is solved
    // first, matching Lean's `split` ordering where the positive case leads).
    let false_goal = Goal {
        meta_id: false_meta,
        target: false_target,
        local_ctx: false_ctx,
        tag: None,
    };
    let true_goal = Goal {
        meta_id: true_meta,
        target: true_target,
        local_ctx: true_ctx,
        tag: None,
    };
    state.goals.push_front(false_goal);
    state.goals.push_front(true_goal);
    Ok(())
}

/// A decomposed `@ite.{u} α c inst a b` application.
struct IteApp {
    /// Universe levels on the `ite` constant (its single param `u`).
    levels: Vec<Level>,
    /// Result type `α`.
    alpha: Expr,
    /// Condition `c : Prop`.
    cond: Expr,
    /// `Decidable c` instance.
    inst: Expr,
    /// `then` value `a : α`.
    then_val: Expr,
    /// `else` value `b : α`.
    else_val: Expr,
}

impl IteApp {
    /// Reconstruct the full `@ite.{u} α c inst a b` application.
    fn rebuild(&self) -> Expr {
        self.with_inst(self.inst.clone())
    }

    /// Reconstruct `@ite.{u} α c <inst> a b` with the instance argument
    /// replaced by `inst`.
    fn with_inst(&self, inst: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("ite"), self.levels.clone()),
            [
                self.alpha.clone(),
                self.cond.clone(),
                inst,
                self.then_val.clone(),
                self.else_val.clone(),
            ],
        )
    }
}

/// Match `@ite.{u} α c inst a b` (exactly 5 args, head const `ite`).
fn match_ite(expr: &Expr) -> Option<IteApp> {
    let head = expr.get_app_fn();
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("ite") {
        return None;
    }
    let args = expr.get_app_args();
    if args.len() != 5 {
        return None;
    }
    Some(IteApp {
        levels: levels.to_vec(),
        alpha: args[0].clone(),
        cond: args[1].clone(),
        inst: args[2].clone(),
        then_val: args[3].clone(),
        else_val: args[4].clone(),
    })
}

/// Find the first `ite` subterm in `expr` in a deterministic pre-order
/// traversal (head-first, then arguments/binder-bodies left-to-right).
fn find_first_ite(expr: &Expr) -> Option<IteApp> {
    crate::stack_safe(|| {
        if let Some(ite) = match_ite(expr) {
            return Some(ite);
        }
        match expr.kind() {
            ExprKind::App(f, a) => find_first_ite(f).or_else(|| find_first_ite(a)),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                find_first_ite(ty).or_else(|| find_first_ite(body))
            }
            ExprKind::Let(_, ty, val, body, _) => find_first_ite(ty)
                .or_else(|| find_first_ite(val))
                .or_else(|| find_first_ite(body)),
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => find_first_ite(inner),
            _ => None,
        }
    })
}

/// The `and_intros` tactic repeatedly applies `And.intro` to the goal,
/// splitting a (possibly nested) conjunction into one subgoal per conjunct.
///
/// This mirrors Mathlib's `and_intros` (`Mathlib/Tactic/Constructor.lean`),
/// which runs `apply And.intro` until it no longer makes progress. For a goal
/// `A ∧ B ∧ C`, it produces three subgoals `A`, `B`, `C` (in left-to-right
/// order) rather than the single subgoal pair that one `constructor`/`split`
/// step would leave.
///
/// Unlike `constructor`, it does not split `Iff`; only `And` is flattened, so
/// the conjuncts retain their original logical form.
///
/// # Soundness
///
/// The entire conjunction tree is closed with a single kernel-checked
/// `And.intro` proof term (built by [`build_and_intro_proof`]). The leaves of
/// the tree become fresh metavariable subgoals, so every closure flows through
/// `close_goal`'s type check. When the goal is not a conjunction, the tactic
/// succeeds without changing the state (matching Mathlib's `repeat'`, which
/// permits zero iterations).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the original goal is closed with a kernel-checked nested
///   `And.intro` term, and one subgoal per leaf conjunct is pushed in
///   left-to-right order
/// ENSURES: On Ok, a non-conjunction goal is left unchanged
pub fn and_intros(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Build the nested And.intro proof term and collect the leaf conjuncts.
    let mut leaves: Vec<Expr> = Vec::new();
    let proof = build_and_intro_proof(state, &goal, &goal.target, &mut leaves);

    // No conjunction at the top level: nothing to do (matches `repeat'`).
    if leaves.len() <= 1 {
        return Ok(());
    }

    // Allocate a fresh metavariable per leaf and splice them into the proof.
    let mut leaf_goals = Vec::with_capacity(leaves.len());
    let mut subst = Vec::with_capacity(leaves.len());
    for leaf_ty in &leaves {
        let leaf_ty = state.metas.instantiate(leaf_ty);
        let meta_id = state.fresh_meta(leaf_ty.clone());
        let meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_id)));
        leaf_goals.push(Goal {
            meta_id,
            target: leaf_ty,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        });
        subst.push(meta_expr);
    }
    let mut subst_iter = subst.into_iter();
    let proof = instantiate_and_intro_leaves(proof, &mut subst_iter);

    // Close the original goal with the single kernel-checked And.intro tree.
    state.close_goal(&goal, proof)?;

    // Push the leaf subgoals to the front in left-to-right order.
    for leaf in leaf_goals.into_iter().rev() {
        state.goals.push_front(leaf);
    }
    Ok(())
}

/// Recursively build a nested `And.intro` proof term for `target`, collecting
/// the conjunct leaf types into `leaves` (left-to-right). Leaves are recorded
/// as placeholder positions: the returned term contains [`Expr::sort`]-tagged
/// holes that [`instantiate_and_intro_leaves`] replaces with subgoal metas.
///
/// A leaf is any subterm whose WHNF head is not `And`. The proof term skeleton
/// uses a unique sentinel ([`and_intro_hole`]) per leaf so the caller can splice
/// fresh metavariables in the same left-to-right order they were discovered.
fn build_and_intro_proof(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    leaves: &mut Vec<Expr>,
) -> Expr {
    let whnf = state.whnf(goal, target);
    let head = whnf.get_app_fn().clone();
    let args: Vec<Expr> = whnf.get_app_args().into_iter().cloned().collect();

    if let ExprKind::Const(name, levels) = head.kind() {
        if *name == Name::from_string("And") && args.len() == 2 {
            let left = build_and_intro_proof(state, goal, &args[0], leaves);
            let right = build_and_intro_proof(state, goal, &args[1], leaves);
            let mut proof = Expr::const_(Name::from_string("And.intro"), levels.clone());
            proof = Expr::app(proof, args[0].clone());
            proof = Expr::app(proof, args[1].clone());
            proof = Expr::app(proof, left);
            proof = Expr::app(proof, right);
            return proof;
        }
    }

    // Leaf conjunct: record its type and emit a placeholder hole.
    leaves.push(target.clone());
    and_intro_hole()
}

/// A unique placeholder marking a leaf position in the `And.intro` skeleton.
///
/// Uses a distinguished local constant name that cannot collide with a real
/// proof term; [`instantiate_and_intro_leaves`] rewrites every occurrence,
/// left-to-right, into the freshly-allocated subgoal metavariable.
fn and_intro_hole() -> Expr {
    Expr::const_(Name::from_string("_clean.and_intros.hole"), vec![])
}

/// Replace each leaf hole in `proof` (left-to-right) with the next metavariable
/// expression from `metas`. The traversal order matches the order in which
/// [`build_and_intro_proof`] pushed leaves, so subgoal `i` lands in conjunct `i`.
fn instantiate_and_intro_leaves(proof: Expr, metas: &mut impl Iterator<Item = Expr>) -> Expr {
    match proof.kind() {
        ExprKind::Const(name, _) if *name == Name::from_string("_clean.and_intros.hole") => {
            // Each hole is consumed exactly once; if the iterator is exhausted
            // the skeleton is malformed, so leave the hole in place (the
            // subsequent kernel type-check will reject it rather than panic).
            metas.next().unwrap_or(proof)
        }
        ExprKind::App(f, a) => {
            let f = instantiate_and_intro_leaves(f.as_ref().clone(), metas);
            let a = instantiate_and_intro_leaves(a.as_ref().clone(), metas);
            Expr::app(f, a)
        }
        _ => proof,
    }
}

/// Solve the left branch of a disjunction by reducing goal to its left side.
///
/// For goal `Or A B`, creates a subgoal `A` and closes the current goal with
/// `Or.inl A B ?proof`.
pub fn left_(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let target = state.whnf(&goal, &goal.target);
    let head = target.get_app_fn().clone();
    let args: Vec<Expr> = target.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, levels) if *name == Name::from_string("Or") => {
            if args.len() != 2 {
                return Err(TacticError::GoalMismatch(
                    "left requires goal of form Or a b".to_string(),
                ));
            }

            let left_ty = state.metas.instantiate(&args[0]);
            let left_meta_id = state.fresh_meta(left_ty.clone());
            let left_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(left_meta_id)));

            // Build Or.inl a b ?proof
            let mut proof = Expr::const_(Name::from_string("Or.inl"), levels.clone());
            proof = Expr::app(proof, args[0].clone());
            proof = Expr::app(proof, args[1].clone());
            proof = Expr::app(proof, left_meta.clone());

            // Part of #2154: type-check Or.inl proof before accepting
            state.close_goal(&goal, proof)?;

            let left_goal = Goal {
                meta_id: left_meta_id,
                target: left_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            };
            state.goals.push_front(left_goal);
            Ok(())
        }
        _ => Err(TacticError::GoalMismatch(
            "left requires goal of form Or a b".to_string(),
        )),
    }
}

/// Solve the right branch of a disjunction by reducing goal to its right side.
///
/// For goal `Or A B`, creates a subgoal `B` and closes the current goal with
/// `Or.inr A B ?proof`.
pub fn right_(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let target = state.whnf(&goal, &goal.target);
    let head = target.get_app_fn().clone();
    let args: Vec<Expr> = target.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, levels) if *name == Name::from_string("Or") => {
            if args.len() != 2 {
                return Err(TacticError::GoalMismatch(
                    "right requires goal of form Or a b".to_string(),
                ));
            }

            let right_ty = state.metas.instantiate(&args[1]);
            let right_meta_id = state.fresh_meta(right_ty.clone());
            let right_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(right_meta_id)));

            // Build Or.inr a b ?proof
            let mut proof = Expr::const_(Name::from_string("Or.inr"), levels.clone());
            proof = Expr::app(proof, args[0].clone());
            proof = Expr::app(proof, args[1].clone());
            proof = Expr::app(proof, right_meta.clone());

            // Part of #2154: type-check Or.inr proof before accepting
            state.close_goal(&goal, proof)?;

            let right_goal = Goal {
                meta_id: right_meta_id,
                target: right_ty,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            };
            state.goals.push_front(right_goal);
            Ok(())
        }
        _ => Err(TacticError::GoalMismatch(
            "right requires goal of form Or a b".to_string(),
        )),
    }
}

// =============================================================================
// Contradiction and False-elimination tactics
// =============================================================================

/// The `exfalso` tactic changes the goal to `False`.
///
/// This is useful when we want to derive a contradiction to prove any proposition.
/// It applies the principle of explosion (ex falso quodlibet): from False, anything follows.
///
/// # Example
/// ```text
/// Goal: P
/// exfalso
/// Goal: False
/// ```
///
/// The proof term is `False.elim {P} <proof of False>`.
pub fn exfalso(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Check that False.elim exists
    let false_elim_name = Name::from_string("False.elim");
    if state.env.get_const(&false_elim_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "False.elim".to_string(),
        });
    }

    // Create a new goal for False
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let new_meta_id = state.fresh_meta(false_type.clone());

    // The proof is: False.elim {goal.target} <new_meta>
    // False.elim : {C : Sort u} → False → C
    // Universe zero correct: contradiction goals target Prop (Sort 0)
    let false_elim = Expr::const_(false_elim_name, vec![Level::zero()]);
    let proof = Expr::app(
        Expr::app(false_elim, goal.target.clone()),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id))),
    );

    // Part of #2154: type-check False.elim proof before accepting
    state.close_goal(&goal, proof)?;

    // Add the new goal (prove False)
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: false_type,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);

    Ok(())
}

/// The `contradiction` tactic proves the goal by finding contradictory hypotheses.
///
/// It searches the local context for:
/// 1. A hypothesis `h : False` (directly proves any goal)
/// 2. A pair `h1 : P` and `h2 : ¬P` (or `h2 : P → False`)
///
/// # Example
/// ```text
/// h1 : P
/// h2 : ¬P
/// Goal: Q
/// contradiction  -- applies absurd h1 h2
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed via `False.elim` or `absurd`
/// ENSURES: On Ok, `close_goal` type-checks the proof (soundness)
/// ENSURES: On Err(NoProgress), no `h : False` or `h1 : P, h2 : ¬P` pair found
/// ENSURES: Search is O(n²) in hypothesis count (pairwise comparison)
pub fn contradiction(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let false_type = Expr::const_(Name::from_string("False"), vec![]);

    // First, look for h : False in context
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        let ty_whnf = state.whnf(&goal, &ty);

        // Check if this is False
        if state.is_def_eq(&goal, &ty_whnf, &false_type) {
            // Found h : False, use False.elim
            // Universe zero correct: contradiction goals target Prop (Sort 0)
            let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
            let proof = Expr::app(
                Expr::app(false_elim, goal.target.clone()),
                Expr::fvar(decl.fvar),
            );
            // Part of #2154: type-check False.elim proof before accepting
            return state.close_goal(&goal, proof);
        }
    }

    // Second, look for h1 : P and h2 : P → False (i.e., ¬P)
    for decl1 in &goal.local_ctx {
        let ty1 = state.metas.instantiate(&decl1.ty);
        let ty1_whnf = state.whnf(&goal, &ty1);

        for decl2 in &goal.local_ctx {
            if decl1.fvar == decl2.fvar {
                continue;
            }

            let ty2 = state.metas.instantiate(&decl2.ty);
            let ty2_whnf = state.whnf(&goal, &ty2);

            // Check if ty2 is ty1 → False (i.e., ¬ty1)
            if let ExprKind::Pi(_, domain, codomain) = ty2_whnf.kind() {
                let domain_whnf = state.whnf(&goal, domain);
                let codomain_whnf = state.whnf(&goal, codomain);

                if state.is_def_eq(&goal, &domain_whnf, &ty1_whnf)
                    && state.is_def_eq(&goal, &codomain_whnf, &false_type)
                {
                    // Found h1 : P and h2 : P → False
                    // Use absurd if available, otherwise construct False.elim (h2 h1)
                    let absurd_name = Name::from_string("absurd");
                    if state.env.get_const(&absurd_name).is_some() {
                        // absurd : {a : Prop} → {b : Sort u} → a → ¬a → b
                        // Universe zero correct: contradiction goals target Prop (Sort 0)
                        let absurd = Expr::const_(absurd_name, vec![Level::zero()]);
                        let proof = Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(absurd, ty1_whnf.clone()), goal.target.clone()),
                                Expr::fvar(decl1.fvar),
                            ),
                            Expr::fvar(decl2.fvar),
                        );
                        // Part of #2154: type-check absurd proof before accepting
                        return state.close_goal(&goal, proof);
                    }
                    // Fallback: False.elim {goal} (h2 h1)
                    // Universe zero correct: contradiction goals target Prop (Sort 0)
                    let false_elim =
                        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
                    let proof = Expr::app(
                        Expr::app(false_elim, goal.target.clone()),
                        Expr::app(Expr::fvar(decl2.fvar), Expr::fvar(decl1.fvar)),
                    );
                    // Part of #2154: type-check False.elim proof before accepting
                    return state.close_goal(&goal, proof);
                }
            }
        }
    }

    Err(TacticError::NoProgress {
        tactic: "contradiction".into(),
    })
}

/// The `by_contra` tactic proves the goal by contradiction (classical reasoning).
///
/// It introduces `h : ¬goal` as a hypothesis and changes the goal to `False`.
/// Uses `Classical.byContradiction : {p : Prop} → (¬p → False) → p`.
///
/// # Example
/// ```text
/// Goal: P
/// by_contra h
/// h : ¬P (i.e., P → False)
/// Goal: False
/// ```
///
/// The proof term is `Classical.byContradiction {P} (fun h : ¬P => <proof of False>)`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `Classical.byContradiction` exists in the environment
/// ENSURES: On Ok, original goal is closed with `byContradiction` proof
/// ENSURES: On Ok, new goal `False` is pushed with `h : ¬goal` in context
/// ENSURES: On Err(EnvironmentMissing), `Classical.byContradiction` not loaded
pub fn by_contra(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Check that Classical.byContradiction exists
    let by_contradiction_name = Name::from_string("Classical.byContradiction");
    if state.env.get_const(&by_contradiction_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Classical.byContradiction".to_string(),
        });
    }

    let false_type = Expr::const_(Name::from_string("False"), vec![]);

    // The negation of the goal: goal → False
    let neg_goal = Expr::pi(BinderInfo::Default, goal.target.clone(), false_type.clone());

    // Create a fresh fvar for the new hypothesis h : ¬goal
    let hyp_fvar = state.fresh_fvar();

    // Create the new local context with h : ¬goal
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx.push(LocalDecl {
        fvar: hyp_fvar,
        name: hyp_name.to_string(),
        ty: neg_goal.clone(),
        value: None,
    });

    // Create a new goal for False
    let new_meta_id = state.fresh_meta_in_context(false_type.clone(), &new_ctx);

    // The proof is: Classical.byContradiction {goal.target} (fun h : ¬goal => <new_meta>)
    // byContradiction : {p : Prop} → (¬p → False) → p
    let by_contradiction = Expr::const_(by_contradiction_name, vec![]);
    let inner_lambda = Expr::lam(
        BinderInfo::Default,
        neg_goal,
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id))).abstract_fvar(hyp_fvar),
    );
    let proof = Expr::app(
        Expr::app(by_contradiction, goal.target.clone()),
        inner_lambda,
    );

    // Type-check: byContradiction proof is synthetically constructed (#2159)
    state.close_goal(&goal, proof)?;

    // Add the new goal (prove False with h : ¬goal in context)
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: false_type,
        local_ctx: new_ctx,
        tag: None,
    };
    state.goals.push_front(new_goal);

    Ok(())
}
