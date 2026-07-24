// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lightweight `decide` tactic for decidable propositions.
//!
//! Closes goals that are decidable propositions by evaluation:
//! synthesizes a `Decidable` instance for the goal type, evaluates the
//! decision procedure via WHNF reduction, and extracts the proof from
//! `Decidable.isTrue`.
//!
//! This is the kernel-reduction-based decide path. For the full SMT-backed
//! decide, see `smt/decide/mod.rs`.
//!
//! Part of #3082.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind};

use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::nat_expr_eval::eval_nat_expr;
use super::norm_num::{eval_int_expr, try_eval_comparison};
use super::proof_term::rfl;
use crate::ElabCtx;

/// Synthesize a `Decidable` expression for the given proposition.
///
/// Attempts to build a `Decidable p` term by recognizing common decidable
/// forms:
/// - `True` → `Decidable.isTrue True.intro`
/// - `False` → `Decidable.isFalse id`
/// - `@Eq T a b` where T has `DecidableEq` → `T.decEq a b`
/// - Boolean operations → structural
///
/// # Contract
///
/// REQUIRES: `target` is a well-formed Prop expression
/// ENSURES: On `Some(d)`, `d` has type `Decidable target`
/// ENSURES: On `None`, no decidable instance could be synthesized
fn synthesize_decidable(state: &ProofState, target: &Expr) -> Option<Expr> {
    // True
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        return Some(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                target.clone(),
            ),
            Expr::const_(Name::from_string("True.intro"), vec![]),
        ));
    }

    // False
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("False")) {
        return Some(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                target.clone(),
            ),
            // id : False → False
            Expr::lam(BinderInfo::Default, target.clone(), Expr::bvar(0)),
        ));
    }

    // Equality: @Eq T a b → T.decEq a b
    if let Ok((ty, lhs, rhs, _levels)) = match_equality(target) {
        let type_head = ty.get_app_fn();
        if let ExprKind::Const(type_name, _) = type_head.kind() {
            let dec_eq_name = Name::from_string(&format!("{type_name}.decEq"));
            if state.env().get_const(&dec_eq_name).is_some() {
                return Some(Expr::apps(Expr::const_(dec_eq_name, vec![]), [lhs, rhs]));
            }
        }
    }

    // Bool comparisons
    if let ExprKind::Const(name, _) = target.get_app_fn().kind() {
        let name_str = name.to_string();
        // BEq.beq, decide for Bool-valued operations
        if name_str.contains("BEq") || name_str.contains("Bool") {
            // Try to evaluate as a decidable Bool operation via native reduction
            return None; // Fall through to WHNF evaluation
        }
    }

    None
}

/// Try to evaluate a Decidable expression to its constructor via WHNF.
///
/// Returns `Some(proof)` if the expression reduces to `Decidable.isTrue proof`,
/// `None` if it reduces to `Decidable.isFalse` or does not reduce.
fn eval_decidable(
    state: &ProofState,
    goal: &super::core::Goal,
    decidable_expr: &Expr,
) -> Option<Expr> {
    let reduced = state.whnf(goal, decidable_expr);
    let head = reduced.get_app_fn();

    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Decidable.isTrue") {
            // Extract the proof payload (last argument)
            let args = reduced.get_app_args();
            return args.last().map(|p| (*p).clone());
        }
    }

    None
}

/// Try to prove `target` by resolving a `Decidable target` instance through the
/// proper recursive resolver (`ElabCtx::resolve_instance`) and reducing it via
/// kernel WHNF, extracting the `Decidable.isTrue` witness.
///
/// This is the kernel-reduction `decide` lane: it closes ground decidable goals
/// (finite-`Fintype` `∀`, `List`/`Int` equality, concrete `select`/`store`, …)
/// with a kernel-checked proof term, BYPASSING `super::smt::decide` (which can
/// embed `trustedAy` axioms — a TCB hole). `resolve_instance` does the full
/// recursive class search the ad-hoc `synthesize_decidable` cannot.
///
/// Returns `None` (state unchanged) when no `Decidable` instance resolves or the
/// instance does not WHNF-reduce to `isTrue`, so the caller falls through to SMT.
///
/// # Contract
/// REQUIRES: `target` is the (instantiated) goal proposition.
/// ENSURES: On `Some(h)`, `h` is the `isTrue` payload (`h : target`), re-checked
/// by the kernel in `close_goal`; a false goal cannot produce a witness here.
fn try_decide_by_kernel_reduction(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
) -> Option<Expr> {
    let decidable_target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        target.clone(),
    );
    // Scope `ctx` so its `&Environment` borrow of `state` ends before the
    // `eval_decidable(state, …)` call below. Crucially, INSTANTIATE the resolved
    // instance's metavariables: `resolve_instance` assigns the deferred
    // dependent-instance args (e.g. the `[DecidableEq α]` of
    // `instDecidableEqList`) as metavars in `ctx.metas` but leaves them
    // un-substituted in the returned term. A metavar-bearing instance is an
    // opaque redex that `eval_decidable`'s WHNF cannot reduce to
    // `Decidable.isTrue`, so the lane would silently fall through to SMT. The
    // instantiated term is ground and owned, so nothing borrowed from `ctx`
    // escapes the block.
    let inst_expr = {
        let mut ctx = ElabCtx::new(state.env());
        let resolved = ctx.resolve_instance(&decidable_target)?;
        ctx.metas.instantiate(&resolved)
    };
    eval_decidable(state, goal, &inst_expr)
}

/// Check if a goal can be closed by ground numeric evaluation.
///
/// Returns `true` if the proposition evaluates to `true` by numeric
/// computation (equality, comparisons for Nat and Int).
fn is_numerically_decidable(target: &Expr) -> bool {
    // Comparisons
    if try_eval_comparison(target).is_some() {
        return true;
    }

    // Equalities
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(target) {
        if eval_nat_expr(&lhs).is_some() && eval_nat_expr(&rhs).is_some() {
            return true;
        }
        if eval_int_expr(&lhs).is_some() && eval_int_expr(&rhs).is_some() {
            return true;
        }
    }

    false
}

/// Lightweight decide tactic for decidable propositions.
///
/// Closes goals that are decidable propositions by:
/// 1. Synthesizing a `Decidable` instance for the goal type
/// 2. Evaluating the decision procedure via WHNF reduction
/// 3. Extracting the proof from `Decidable.isTrue`
///
/// # Supported propositions
///
/// - `True`, `False`
/// - `a = b` where the type has `DecidableEq` (Bool, Nat, Int, finite enums)
/// - Nat/Int comparisons (`<`, `<=`, `>`, `>=`)
/// - Bool operations (via WHNF reduction)
///
/// # Algorithm
///
/// 1. If the goal is `True`, close with `True.intro`
/// 2. If the goal is a ground numeric proposition, evaluate and use `rfl`
/// 3. Synthesize a `Decidable` instance for the goal
/// 4. Reduce the instance via WHNF
/// 5. If it yields `isTrue proof`, close with `proof`
/// 6. Otherwise fall back to the SMT `decide` tactic
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed with a type-checked proof term
/// ENSURES: On Err, the proposition is not decidable or evaluates to false
pub fn eval_decide(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Fast path: True
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        let proof = Expr::const_(Name::from_string("True.intro"), vec![]);
        return state.close_goal(&goal, proof);
    }

    // Fast path: ground numeric equality — try rfl
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(&target) {
        // Nat equality
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::InvalidTarget {
                tactic: "decide".into(),
                detail: format!("equality is false: {l} != {r}"),
            });
        }
        // Int equality
        if let (Some(l), Some(r)) = (eval_int_expr(&lhs), eval_int_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::InvalidTarget {
                tactic: "decide".into(),
                detail: format!("equality is false: {l} != {r}"),
            });
        }
    }

    // Fast path: ground numeric comparisons
    if let Some(result) = try_eval_comparison(&target) {
        if !result {
            return Err(TacticError::InvalidTarget {
                tactic: "decide".into(),
                detail: "comparison is false".into(),
            });
        }
        // Comparison is true — close ground Int `<=` / `<` goals with a
        // constructive `Int.NonNeg.mk` witness. The Int decidability instances
        // (`instDecidableIntLe` / `instDecidableIntLt`) are non-computational
        // axioms, so the WHNF-reduction path below cannot extract a sound proof
        // for Int; without this the goal would fall through to SMT `decide`.
        // Nat comparisons are handled by the existing reduction path.
        if super::norm_num_ext::try_close_int_ground_comparison(state, &goal).is_some() {
            return Ok(());
        }
        // Ground Nat `<=` / `<` / `>=` / `>` goals are closed with a
        // constructive `Nat.le.refl` / `Nat.le.step` chain. The native
        // `Nat.decLe` / `Nat.decLt` reducers emit `Decidable.isTrue sorryAx`,
        // so the WHNF-reduction path below would extract `sorryAx`; the `>` /
        // bare `Nat.gt` / bare `Nat.ge` shapes also have no sound decide path.
        if super::norm_num_ext::try_close_nat_ground_comparison(state, &goal).is_some() {
            return Ok(());
        }
        // Otherwise need a proof term from the decide instance (Nat path).
    }

    // Ground disequality `a ≠ b`: Lean's `decide` closes these. Route through
    // the noConfusion disequality builder so the proof stays kernel-checkable
    // and axiom-free (the native `Nat.decEq` reducer only yields
    // `Decidable.isFalse sorryAx`, which is unsound to extract). On failure,
    // fall through to the remaining paths. Part of the tactic-divergence
    // parity work.
    if super::decide_eq::match_ne(&target).is_some()
        && super::decide_eq::try_close_ne_by_noconfusion(state).is_ok()
    {
        return Ok(());
    }

    // `Not (Eq α a b)` is definitionally the same proposition as `Ne α a b`,
    // but the surface `Not (a = b)` form does not match the `Ne` head, so the
    // noConfusion lane above is skipped. Route it through the same builder when
    // the operands are distinct decidable constructors. The proof has type
    // `Eq α a b → False`, which is def-eq to `Not (Eq α a b)`; `close_goal`
    // re-checks it against the goal so a true equality cannot be closed here.
    if let Some((ne_ty, lhs, rhs)) = match_not_eq(&target) {
        if super::decide_eq::decidable_type_check(&ne_ty) {
            let eq_level = state
                .infer_type(&goal, &ne_ty)
                .ok()
                .and_then(|sort| match sort.kind() {
                    ExprKind::Sort(level) => Some(level.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| clean_kernel::Level::succ(clean_kernel::Level::zero()));
            if let Some(ne_proof) = super::decide_eq_noconfusion::build_noconfusion_ne_proof(
                state.env(),
                &ne_ty,
                &lhs,
                &rhs,
                &eq_level,
            ) {
                if state.close_goal(&goal, ne_proof).is_ok() {
                    return Ok(());
                }
            }
        }
    }

    // Plain decidable equality `a = b` (e.g. `some 3 = some 3`): route through
    // `decide_eq`, which closes a true equality reflexively / by reduction and
    // builds a kernel-checkable `Decidable.isFalse` (noConfusion) term for a
    // genuinely-false one. For a false equality this returns Err and we fall
    // through to SMT, which reports `Refuted` — the goal stays unproved (sound).
    if let Ok((eq_ty, _lhs, _rhs, _levels)) = match_equality(&target) {
        if super::decide_eq::decidable_type_check(&eq_ty)
            && super::decide_eq::decide_eq(state).is_ok()
        {
            return Ok(());
        }
    }

    // BEq shape `(a == b) = true` / `(a == b) = false`: reduce the `BEq.beq`
    // application via WHNF and check it matches the asserted Bool literal. For
    // the supported decidable types `==` δι-reduces to a `Bool` constructor, so
    // the goal becomes a ground `Bool` equality closed reflexively. A mismatch
    // (e.g. `(some 3 == some 4) = true`) leaves the goal for the SMT fallback.
    if try_close_beq_eq_bool(state, &goal, &target).is_ok() {
        return Ok(());
    }

    // Try to synthesize a Decidable instance
    if let Some(decidable_expr) = synthesize_decidable(state, &target) {
        // Evaluate via WHNF
        if let Some(proof) = eval_decidable(state, &goal, &decidable_expr) {
            return state.close_goal(&goal, proof);
        }
    }

    // Kernel-reduction lane: resolve a `Decidable target` instance via the proper
    // recursive resolver and extract the `isTrue` witness by WHNF. This closes
    // ground decidable goals with a kernel-checked term BEFORE any SMT call,
    // removing `super::smt::decide` (which can embed `trustedAy`) from the TCB for
    // this class. `close_goal` re-checks the witness, so a false goal cannot slip
    // through (it returns `None`/`Err` here and falls through to SMT, which
    // `Refuted`s it).
    if let Some(proof) = try_decide_by_kernel_reduction(state, &goal, &target) {
        return state.close_goal(&goal, proof);
    }

    // Fall back to SMT decide (non-decidable / arithmetic goals, or instances
    // that do not kernel-reduce to `isTrue`).
    super::smt::decide(state)
}

/// Match `Not (@Eq α a b)` and return `(α, a, b)`.
///
/// REQUIRES: `expr` is a well-formed expression.
/// ENSURES: Returns `Some((α, a, b))` iff `expr` is `Not p` with `p = @Eq α a b`.
fn match_not_eq(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Not") && args.len() == 1 {
            if let Ok((ty, lhs, rhs, _levels)) = match_equality(args[0]) {
                return Some((ty, lhs, rhs));
            }
        }
    }
    None
}

/// Close a `(a == b) = bool_lit` goal by reducing the `BEq.beq` application and
/// comparing against the asserted `Bool` literal.
///
/// Returns `Ok(())` on success (goal closed reflexively after WHNF), and an
/// error otherwise so the caller can fall through to the SMT path.
fn try_close_beq_eq_bool(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
) -> TacticResult {
    let Ok((_bool_ty, lhs, rhs, _levels)) = match_equality(target) else {
        return Err(TacticError::GoalMismatch("not an equality".into()));
    };
    // One side must be a literal Bool constant; the other the `==` application.
    let is_bool_lit = |e: &Expr| {
        matches!(e.kind(), ExprKind::Const(n, _)
            if n == &Name::from_string("Bool.true") || n == &Name::from_string("Bool.false")
            || n == &Name::from_string("true") || n == &Name::from_string("false"))
    };
    let (beq_app, bool_lit) = if is_bool_lit(&rhs) {
        (lhs, rhs)
    } else if is_bool_lit(&lhs) {
        (rhs, lhs)
    } else {
        return Err(TacticError::GoalMismatch("no Bool literal side".into()));
    };
    // The non-literal side must be a `BEq.beq` / `==` application.
    let head = beq_app.get_app_fn();
    let is_beq = matches!(head.kind(), ExprKind::Const(n, _)
        if n.to_string().contains("BEq.beq") || n.to_string() == "beq");
    if !is_beq {
        return Err(TacticError::GoalMismatch("not a BEq application".into()));
    }
    // Reduce the `==` application and require it to converge with the asserted
    // Bool literal. `rfl` re-derives a kernel-checked proof of the whole
    // `(a == b) = lit` goal; the kernel re-checks it in `close_goal`, so a
    // false claim (where `==` reduces to the other literal) is rejected.
    let reduced = state.whnf(goal, &beq_app);
    if state.is_def_eq(goal, &reduced, &bool_lit) {
        return rfl(state);
    }
    Err(TacticError::GoalMismatch(
        "BEq did not reduce to literal".into(),
    ))
}
