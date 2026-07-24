// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decidable equality tactics
//!
//! Tactics for proving goals involving decidable equality, such as
//! `Decidable (a = b)` or direct equality goals `a = b` for types
//! with `DecidableEq` instances.

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;
use crate::tactic::calc::make_eq_refl;
use crate::tactic::decide_eq_noconfusion::build_noconfusion_ne_proof;
use crate::tactic::equality::match_equality;
use crate::tactic::{reduce_eq, rfl, Goal, ProofState, TacticError, TacticResult};

/// Prove goals of the form `Decidable (a = b)` or close `a = b` when decidable.
///
/// This tactic handles decidable equality in two ways:
/// 1. If goal is `Decidable (a = b)`, construct a `Decidable` instance
/// 2. If goal is `a = b` where the type has decidable equality, use `decide`
///
/// Works for types with `DecidableEq` instances (Nat, Bool, Fin, `List α`, etc.)
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Goal target matches `Decidable (a = b)` or `@Eq α a b` pattern
/// ENSURES: On Ok, the current goal is closed with a proof term
/// ENSURES: On Err(GoalMismatch), goal is neither `Decidable (a = b)` nor equality; state unchanged
/// ENSURES: On Err(ArithmeticFailed), type lacks decidable equality; state unchanged
pub fn decide_eq(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Check if goal is Decidable (a = b)
    if let Some((eq_ty, lhs, rhs)) = match_decidable_eq(&target) {
        // Build DecidableEq instance check
        return decide_eq_check(state, &goal, &eq_ty, &lhs, &rhs);
    }

    // Check if goal is an equality a = b with decidable type
    if let Ok((ty, lhs, rhs, _levels)) = match_equality(&target) {
        // Try to evaluate equality decision
        return decide_eq_equality(state, &goal, &ty, &lhs, &rhs);
    }

    Err(TacticError::GoalMismatch(
        "decide_eq: goal must be `Decidable (a = b)` or an equality with decidable type"
            .to_string(),
    ))
}

/// Match `@Ne α a b` pattern (negated equality).
///
/// `Ne α a b` is the reducible definition `Not (Eq α a b) = (Eq α a b → False)`,
/// so a proof of `Ne α a b` is exactly a proof of `Eq α a b → False`.
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `Some((levels, α, a, b))` iff `expr` is `@Ne.{levels} α a b`
///   with exactly 3 arguments
/// ENSURES: Returns `None` for all other expression forms
pub(crate) fn match_ne(expr: &Expr) -> Option<(Vec<Level>, Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    if let ExprKind::Const(name, levels) = head.kind() {
        if name == &Name::from_string("Ne") && args.len() == 3 {
            return Some((
                levels.to_vec(),
                args[0].clone(), // type α
                args[1].clone(), // lhs a
                args[2].clone(), // rhs b
            ));
        }
    }
    None
}

/// Close a `@Ne α a b` goal by constructing a kernel-checkable disequality
/// proof via `α.noConfusion`.
///
/// In Lean 4 both `decide` and `norm_num` close ground disequalities such as
/// `(5 : Nat) ≠ 3`. This routes the goal through the same `build_noconfusion_ne_proof`
/// machinery used by `decide_eq`, producing a proof of `Eq α a b → False`, which
/// is definitionally `Ne α a b` (`Ne` is a reducible definition unfolding to
/// `Not (Eq α a b)`).
///
/// SOUNDNESS: the proof term contains only `α.noConfusion` / `False` /
/// constructor applications — no `sorryAx` and no domain-specific axioms.
/// `close_goal` re-checks the term against the goal via the kernel type checker,
/// so an ill-typed term is rejected (fails closed). The `decide_eq` test
/// `test_decide_eq_list_nat_inequality_no_trusted_axioms` pins `trusted_axiom_count == 0`
/// for the same proof builder.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current `Ne` goal is closed with a type-checked proof term
/// ENSURES: On Err(GoalMismatch), goal is not a `Ne` application; state unchanged
/// ENSURES: On Err(ArithmeticFailed), no constructor-discrimination proof is
///   available (e.g. symbolic operands or unsupported type); state unchanged
pub(crate) fn try_close_ne_by_noconfusion(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let Some((_levels, ne_ty, lhs, rhs)) = match_ne(&target) else {
        return Err(TacticError::GoalMismatch(
            "try_close_ne_by_noconfusion: goal is not a `Ne` application".to_string(),
        ));
    };

    if !decidable_type_check(&ne_ty) {
        return Err(TacticError::ArithmeticFailed {
            tactic: "decide".to_string(),
            reason: format!("type {ne_ty:?} does not support noConfusion disequality"),
        });
    }

    // Universe level of the underlying equality. Infer from the carrier type
    // when possible, defaulting to `1` (the level for `Sort 1` carriers such
    // as Nat/Int/Bool) otherwise.
    let eq_level = state
        .infer_type(&goal, &ne_ty)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .unwrap_or_else(|| Level::succ(Level::zero()));

    let Some(ne_proof) = build_noconfusion_ne_proof(state.env(), &ne_ty, &lhs, &rhs, &eq_level)
    else {
        return Err(TacticError::ArithmeticFailed {
            tactic: "decide".to_string(),
            reason: "no constructor-discrimination disequality proof available".to_string(),
        });
    };

    // close_goal kernel-checks `ne_proof : Eq ne_ty lhs rhs → False` against
    // the goal `Ne ne_ty lhs rhs`; `Ne` is reducible so def-eq succeeds.
    state.close_goal(&goal, ne_proof)
}

/// Match `Decidable (Eq α a b)` pattern.
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `Some((α, a, b))` iff `expr` is `Decidable (@Eq α a b)`
/// ENSURES: Returns `None` for all other expression forms
pub(crate) fn match_decidable_eq(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Decidable") && args.len() == 1 {
            // The argument should be an equality
            if let Ok((ty, lhs, rhs, _)) = match_equality(args[0]) {
                return Some((ty, lhs, rhs));
            }
        }
    }
    None
}

/// Handle Decidable (a = b) goal.
///
/// # Contract
///
/// REQUIRES: `goal.target` matches `Decidable (@Eq eq_ty lhs rhs)`
/// ENSURES: On Ok, goal is closed with `Decidable.isTrue` (equal) or `Decidable.isFalse` (not equal)
/// ENSURES: Equal case uses `Eq.refl` or reduction proof; unequal uses a kernel noConfusion proof when available
/// ENSURES: On Err(ArithmeticFailed), cannot decide equality; state unchanged
fn decide_eq_check(
    state: &mut ProofState,
    goal: &Goal,
    eq_ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> TacticResult {
    // Infer universe level of eq_ty once — used for Eq and Decidable constructions.
    let eq_level = state
        .infer_type(goal, eq_ty)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .unwrap_or_else(|| Level::succ(Level::zero()));

    // Build the equality proposition @Eq.{u} eq_ty lhs rhs — this is the
    // implicit {p : Prop} argument for Decidable.isTrue/isFalse. (#2461)
    let eq_prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![eq_level.clone()]),
                eq_ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    );

    // Check if lhs and rhs are definitionally equal
    // (#2212 pattern fix: use goal's local context so FVars resolve)
    if state.is_def_eq(goal, lhs, rhs) {
        // They're equal, construct @Decidable.isTrue (Eq eq_ty lhs rhs) eq_refl
        let eq_refl = make_eq_refl(state, eq_ty, lhs);
        let is_true = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                eq_prop.clone(),
            ),
            eq_refl,
        );
        // Part of #2154 Tier 0: is_def_eq already verified equality;
        // close_goal re-checks via infer_type + is_def_eq (redundant but safe).
        state.close_goal(goal, is_true)?;
        return Ok(());
    }

    // Try proof-producing WHNF reduction: produces an explicit proof term
    // witnessing that both sides reduce to the same normal form. This handles
    // cases where is_def_eq fails but multi-step reduction succeeds. Part of #685.
    if let Some(eq_proof) = state.prove_eq_by_reduction(goal, eq_ty, lhs, rhs, eq_level.clone()) {
        // @Decidable.isTrue (Eq eq_ty lhs rhs) eq_proof
        let is_true = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                eq_prop.clone(),
            ),
            eq_proof,
        );
        // Part of #2154 Tier 0: prove_eq_by_reduction produced a kernel
        // proof term; close_goal re-checks via infer_type + is_def_eq.
        state.close_goal(goal, is_true)?;
        return Ok(());
    }

    // Try to evaluate and check
    if decidable_type_check(eq_ty) {
        if let Some(ne_proof) = build_noconfusion_ne_proof(state.env(), eq_ty, lhs, rhs, &eq_level)
        {
            let is_false = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                    eq_prop.clone(),
                ),
                ne_proof,
            );
            state.close_goal(goal, is_false)?;
            return Ok(());
        }

        let reason = if exprs_definitely_not_equal(lhs, rhs) {
            format!("structural inequality for {eq_ty:?} has no kernel proof path")
        } else {
            "cannot decide equality".to_string()
        };
        return Err(TacticError::ArithmeticFailed {
            tactic: "decide_eq".to_string(),
            reason,
        });
    }

    Err(TacticError::ArithmeticFailed {
        tactic: "decide_eq".to_string(),
        reason: "cannot decide equality".to_string(),
    })
}

/// Handle a = b goal with decidable type.
///
/// # Contract
///
/// REQUIRES: `goal.target` matches `@Eq ty lhs rhs`
/// REQUIRES: `ty` has decidable equality (per `decidable_type_check`)
/// ENSURES: On Ok, goal is closed with `rfl`, reduction proof, or literal comparison
/// ENSURES: On Err(ArithmeticFailed), type lacks decidable equality or values differ; state unchanged
fn decide_eq_equality(
    state: &mut ProofState,
    goal: &Goal,
    ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> TacticResult {
    // Check if type has decidable equality
    if !decidable_type_check(ty) {
        return Err(TacticError::ArithmeticFailed {
            tactic: "decide_eq".to_string(),
            reason: format!("type {ty:?} does not have decidable equality"),
        });
    }

    // Check if lhs and rhs are definitionally equal
    // (#2212 pattern fix: use goal's local context so FVars resolve)
    if state.is_def_eq(goal, lhs, rhs) {
        // Close with rfl
        return rfl(state);
    }

    // Try proof-producing WHNF reduction: reduces both sides and produces
    // an explicit proof term if they converge. Stronger than is_def_eq for
    // multi-step reductions (delta + iota + beta). Part of #685.
    if reduce_eq(state).is_ok() {
        return Ok(());
    }

    // Try to evaluate both sides to literals and compare
    if let (Some(l_val), Some(r_val)) = (eval_to_nat(lhs), eval_to_nat(rhs)) {
        if l_val == r_val {
            return rfl(state);
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "decide_eq".to_string(),
            reason: format!("{l_val} ≠ {r_val}"),
        });
    }

    Err(TacticError::ArithmeticFailed {
        tactic: "decide_eq".to_string(),
        reason: "cannot evaluate equality".to_string(),
    })
}

/// Check if a type has decidable equality.
///
/// REQUIRES: `ty` is a well-formed type expression
/// ENSURES: Returns `true` iff `ty`'s head constant is a known decidable type
///   (Nat, Bool, Int, Char, String, Fin, UInt8/16/32/64, Unit, Empty,
///   `List α`, `Option α` where `α` is also decidable, `Prod α β` where
///   both `α` and `β` are decidable, or `Sum α β` where both `α` and `β`
///   are decidable)
pub(crate) fn decidable_type_check(ty: &Expr) -> bool {
    let head = ty.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        let args = ty.get_app_args();
        let name_str = name.to_string();
        match name_str.as_str() {
            "Nat" | "Bool" | "Int" | "Char" | "String" | "Fin" | "UInt8" | "UInt16" | "UInt32"
            | "UInt64" | "Unit" | "Empty" => true,
            "List" | "Option" => args
                .first()
                .is_some_and(|elem_ty| decidable_type_check(elem_ty)),
            // Prod α β derives DecidableEq when both components do (Lean 4
            // `instDecidableEqProd`); mirror by requiring both component types.
            "Prod" => {
                args.len() == 2 && decidable_type_check(args[0]) && decidable_type_check(args[1])
            }
            // Sum α β derives DecidableEq when both summands do (Lean 4
            // `instDecidableEqSum`); mirror by requiring both type params.
            "Sum" => {
                args.len() == 2 && decidable_type_check(args[0]) && decidable_type_check(args[1])
            }
            _ => false,
        }
    } else {
        false
    }
}

/// Check if two expressions are definitely not equal (by structure).
///
/// ENSURES: Returns `true` only when structural comparison guarantees inequality
///   (different literals, or different Nat/Bool constructors)
/// ENSURES: Returns `false` when inequality cannot be determined structurally
///   (does NOT mean they are equal)
pub(crate) fn exprs_definitely_not_equal(lhs: &Expr, rhs: &Expr) -> bool {
    // Check for different constructors
    match (lhs.kind(), rhs.kind()) {
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 != l2,
        (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) => {
            // Different constructors like Nat.zero vs Nat.succ
            let s1 = n1.to_string();
            let s2 = n2.to_string();
            (s1.contains("zero") && s2.contains("succ"))
                || (s1.contains("succ") && s2.contains("zero"))
                || (s1 == "Bool.true" && s2 == "Bool.false")
                || (s1 == "Bool.false" && s2 == "Bool.true")
        }
        _ => false,
    }
}

/// Evaluate expression to natural number if possible.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `Some(n)` for Nat literals, `Nat.zero`, and `Nat.succ^k(0)` chains
/// ENSURES: Returns `None` for non-Nat or unevaluable expressions
pub(crate) fn eval_to_nat(expr: &Expr) -> Option<u64> {
    stack_safe(|| match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64(),
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if s == "Nat.zero" || s == "0" {
                Some(0)
            } else {
                None
            }
        }
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    eval_to_nat(arg).map(|n| n + 1)
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Environment;

    fn make_decidable_eq_goal(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        ty,
                    ),
                    lhs,
                ),
                rhs,
            ),
        )
    }

    fn make_eq_goal(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    ty,
                ),
                lhs,
            ),
            rhs,
        )
    }

    fn list_ty(elem_ty: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            elem_ty,
        )
    }

    fn option_ty(elem_ty: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
            elem_ty,
        )
    }

    fn option_none(elem_ty: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
            elem_ty,
        )
    }

    fn option_some(elem_ty: Expr, value: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
                elem_ty,
            ),
            value,
        )
    }

    fn prod_ty(fst_ty: Expr, snd_ty: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod"),
                    vec![Level::zero(), Level::zero()],
                ),
                fst_ty,
            ),
            snd_ty,
        )
    }

    fn prod_mk(fst_ty: Expr, snd_ty: Expr, fst: Expr, snd: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Prod.mk"),
                            vec![Level::zero(), Level::zero()],
                        ),
                        fst_ty,
                    ),
                    snd_ty,
                ),
                fst,
            ),
            snd,
        )
    }

    fn sum_ty(left_ty: Expr, right_ty: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
                left_ty,
            ),
            right_ty,
        )
    }

    fn sum_inl(left_ty: Expr, right_ty: Expr, value: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Sum.inl"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    left_ty,
                ),
                right_ty,
            ),
            value,
        )
    }

    fn sum_inr(left_ty: Expr, right_ty: Expr, value: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Sum.inr"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    left_ty,
                ),
                right_ty,
            ),
            value,
        )
    }

    fn list_nil(elem_ty: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            elem_ty,
        )
    }

    fn list_cons(elem_ty: Expr, head: Expr, tail: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    elem_ty,
                ),
                head,
            ),
            tail,
        )
    }

    fn contains_named_const(expr: &Expr, target: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == target,
            ExprKind::App(f, a) => {
                contains_named_const(f, target) || contains_named_const(a, target)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_named_const(ty, target) || contains_named_const(body, target)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                contains_named_const(ty, target)
                    || contains_named_const(val, target)
                    || contains_named_const(body, target)
            }
            _ => false,
        }
    }

    #[test]
    fn test_decidable_type_check_supports_list_only_when_element_decidable() {
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let undecidable_ty = Expr::const_(Name::from_string("A"), vec![]);

        assert!(
            decidable_type_check(&list_ty(nat_ty)),
            "List Nat should reuse the decide_eq noConfusion lane"
        );
        assert!(
            !decidable_type_check(&list_ty(undecidable_ty)),
            "List A should stay unsupported when the element type is unsupported"
        );
    }

    #[test]
    fn test_decide_eq_list_nat_inequality_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_nat_ty = list_ty(nat_ty.clone());
        let lhs = list_cons(nat_ty.clone(), Expr::nat_lit(1), list_nil(nat_ty.clone()));
        let rhs = list_cons(nat_ty.clone(), Expr::nat_lit(2), list_nil(nat_ty));
        let goal = make_decidable_eq_goal(list_nat_ty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("list inequality should close via List.noConfusion");
        assert!(state.is_complete(), "list inequality goal should be closed");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "list inequality should stay on the kernel proof path"
        );

        let proof = state
            .proof_term()
            .expect("completed list goal should retain the proof term");
        assert!(contains_named_const(&proof, "List.noConfusion"));
        assert!(contains_named_const(&proof, "Nat.noConfusion"));
    }

    #[test]
    fn test_decide_eq_list_nat_reflexive_goal_closes_with_rfl_path() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_nat_ty = list_ty(nat_ty.clone());
        let value = list_cons(nat_ty.clone(), Expr::nat_lit(1), list_nil(nat_ty));
        let goal = make_eq_goal(list_nat_ty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive list equality should close");
        assert!(
            state.is_complete(),
            "reflexive list equality goal should close"
        );
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "reflexive list equality should stay trust-free"
        );
    }

    #[test]
    fn test_decidable_type_check_supports_option_only_when_element_decidable() {
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let undecidable_ty = Expr::const_(Name::from_string("A"), vec![]);

        assert!(
            decidable_type_check(&option_ty(nat_ty)),
            "Option Nat should reuse the decide_eq noConfusion lane"
        );
        assert!(
            !decidable_type_check(&option_ty(undecidable_ty)),
            "Option A should stay unsupported when the element type is unsupported"
        );
    }

    #[test]
    fn test_decidable_type_check_supports_prod_only_when_both_components_decidable() {
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let undecidable_ty = Expr::const_(Name::from_string("A"), vec![]);

        assert!(
            decidable_type_check(&prod_ty(nat_ty.clone(), bool_ty.clone())),
            "Nat x Bool should reuse the decide_eq noConfusion lane"
        );
        assert!(
            !decidable_type_check(&prod_ty(nat_ty, undecidable_ty.clone())),
            "Nat x A should stay unsupported when one component is unsupported"
        );
        assert!(
            !decidable_type_check(&prod_ty(undecidable_ty.clone(), bool_ty)),
            "A x Bool should stay unsupported when one component is unsupported"
        );
    }

    #[test]
    fn test_decide_eq_option_nat_some_reflexive_goal_closes() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let opt_ty = option_ty(nat_ty.clone());
        let value = option_some(nat_ty, Expr::nat_lit(1));
        let goal = make_eq_goal(opt_ty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive `some 1 = some 1` should close");
        assert!(state.is_complete(), "reflexive Option goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "reflexive Option equality should stay trust-free"
        );
    }

    #[test]
    fn test_decide_eq_option_nat_none_reflexive_goal_closes() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let opt_ty = option_ty(nat_ty.clone());
        let value = option_none(nat_ty);
        let goal = make_eq_goal(opt_ty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive `none = none` should close");
        assert!(state.is_complete(), "reflexive `none` goal should close");
        assert_eq!(state.trusted_axiom_count(), 0);
    }

    #[test]
    fn test_decide_eq_option_nat_some_inequality_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let opt_ty = option_ty(nat_ty.clone());
        let lhs = option_some(nat_ty.clone(), Expr::nat_lit(1));
        let rhs = option_some(nat_ty, Expr::nat_lit(2));
        let goal = make_decidable_eq_goal(opt_ty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`some 1 ≠ some 2` should close via Option.noConfusion");
        assert!(state.is_complete(), "Option inequality goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "Option inequality should stay on the kernel proof path"
        );

        let proof = state
            .proof_term()
            .expect("completed Option goal should retain the proof term");
        assert!(contains_named_const(&proof, "Option.noConfusion"));
        assert!(contains_named_const(&proof, "Nat.noConfusion"));
    }

    #[test]
    fn test_decide_eq_option_nat_some_vs_none_inequality_no_trusted_axioms() {
        // #39: the Option `some 1 ≠ none` noConfusion arm now respects the
        // goal's lhs/rhs orientation, so the builder emits a term of type
        // `Eq (Option Nat) (some 1) none → False` (def-eq to the goal). The
        // strict (`infer_only=false`) `close_goal` from #38 accepts it because
        // `@Option.noConfusionType False (some 1) none` δι-reduces to `False`
        // for the distinct-constructor pair. Previously this arm hard-coded
        // `none`=lhs / `some`=rhs, producing a well-typed term of the WRONG
        // orientation (`Eq none (some 1)`) that the strict close rejected.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let opt_ty = option_ty(nat_ty.clone());
        let lhs = option_some(nat_ty.clone(), Expr::nat_lit(1));
        let rhs = option_none(nat_ty);
        let goal = make_decidable_eq_goal(opt_ty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state)
            .expect("`some 1 ≠ none` should close via correctly-oriented Option.noConfusion");
        assert!(
            state.is_complete(),
            "Option some/none inequality goal should close"
        );
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "Option some/none inequality should stay on the kernel proof path"
        );
        let proof = state
            .proof_term()
            .expect("completed goal should retain the proof term");
        assert!(contains_named_const(&proof, "Option.noConfusion"));
    }

    #[test]
    fn test_decide_eq_option_nat_none_vs_some_inequality_no_trusted_axioms() {
        // #39 reversed direction: `none ≠ some 1`. The orientation-preserving
        // arm must build `Eq (Option Nat) none (some 1) → False`.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let opt_ty = option_ty(nat_ty.clone());
        let lhs = option_none(nat_ty.clone());
        let rhs = option_some(nat_ty, Expr::nat_lit(1));
        let goal = make_decidable_eq_goal(opt_ty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state)
            .expect("`none ≠ some 1` should close via correctly-oriented Option.noConfusion");
        assert!(
            state.is_complete(),
            "Option none/some inequality goal should close"
        );
        assert_eq!(state.trusted_axiom_count(), 0);
        let proof = state
            .proof_term()
            .expect("completed goal should retain the proof term");
        assert!(contains_named_const(&proof, "Option.noConfusion"));
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inr_vs_inl_inequality_no_trusted_axioms() {
        // #39 / cross-constructor Sum, reversed (`inr ≠ inl`). The arm must
        // preserve lhs/rhs orientation just like Option none/some.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = sum_inr(nat_ty.clone(), nat_ty.clone(), Expr::nat_lit(2));
        let rhs = sum_inl(nat_ty.clone(), nat_ty, Expr::nat_lit(1));
        let goal = make_decidable_eq_goal(sty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`inr 2 ≠ inl 1` should close via Sum.noConfusion");
        assert!(
            state.is_complete(),
            "Sum inr/inl inequality goal should close"
        );
        assert_eq!(state.trusted_axiom_count(), 0);
        let proof = state
            .proof_term()
            .expect("completed goal should retain the proof term");
        assert!(contains_named_const(&proof, "Sum.noConfusion"));
    }

    #[test]
    fn test_decide_eq_prod_nat_nat_reflexive_goal_closes() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let pty = prod_ty(nat_ty.clone(), nat_ty.clone());
        let value = prod_mk(nat_ty.clone(), nat_ty, Expr::nat_lit(1), Expr::nat_lit(2));
        let goal = make_eq_goal(pty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive `(1,2) = (1,2)` should close");
        assert!(state.is_complete(), "reflexive Prod goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "reflexive Prod equality should stay trust-free"
        );
    }

    #[test]
    fn test_decide_eq_prod_nat_nat_first_component_differs_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let pty = prod_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = prod_mk(
            nat_ty.clone(),
            nat_ty.clone(),
            Expr::nat_lit(1),
            Expr::nat_lit(2),
        );
        let rhs = prod_mk(nat_ty.clone(), nat_ty, Expr::nat_lit(9), Expr::nat_lit(2));
        let goal = make_decidable_eq_goal(pty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`(1,2) ≠ (9,2)` should close via Prod.noConfusion");
        assert!(state.is_complete(), "Prod inequality goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "Prod inequality should stay on the kernel proof path"
        );

        let proof = state
            .proof_term()
            .expect("completed Prod goal should retain the proof term");
        assert!(contains_named_const(&proof, "Prod.noConfusion"));
        assert!(contains_named_const(&proof, "Nat.noConfusion"));
    }

    #[test]
    fn test_decide_eq_prod_nat_nat_second_component_differs_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let pty = prod_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = prod_mk(
            nat_ty.clone(),
            nat_ty.clone(),
            Expr::nat_lit(1),
            Expr::nat_lit(2),
        );
        let rhs = prod_mk(nat_ty.clone(), nat_ty, Expr::nat_lit(1), Expr::nat_lit(3));
        let goal = make_decidable_eq_goal(pty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`(1,2) ≠ (1,3)` should close via Prod.noConfusion");
        assert!(state.is_complete(), "Prod inequality goal should close");
        assert_eq!(state.trusted_axiom_count(), 0);

        let proof = state
            .proof_term()
            .expect("completed Prod goal should retain the proof term");
        assert!(contains_named_const(&proof, "Prod.noConfusion"));
    }

    #[test]
    fn test_decide_eq_nested_option_prod_inequality_closes() {
        // Option (Nat x Nat): some (1,2) ≠ some (1,3) exercises both arms.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let pair_ty = prod_ty(nat_ty.clone(), nat_ty.clone());
        let opt_ty = option_ty(pair_ty.clone());
        let lhs = option_some(
            pair_ty.clone(),
            prod_mk(
                nat_ty.clone(),
                nat_ty.clone(),
                Expr::nat_lit(1),
                Expr::nat_lit(2),
            ),
        );
        let rhs = option_some(
            pair_ty,
            prod_mk(nat_ty.clone(), nat_ty, Expr::nat_lit(1), Expr::nat_lit(3)),
        );
        let goal = make_decidable_eq_goal(opt_ty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state)
            .expect("nested `some (1,2) ≠ some (1,3)` should close via noConfusion");
        assert!(state.is_complete(), "nested Option/Prod goal should close");
        assert_eq!(state.trusted_axiom_count(), 0);

        let proof = state
            .proof_term()
            .expect("completed nested goal should retain the proof term");
        assert!(contains_named_const(&proof, "Option.noConfusion"));
        assert!(contains_named_const(&proof, "Prod.noConfusion"));
    }

    #[test]
    fn test_decide_eq_prod_nat_nat_equal_components_rejects_false_inequality() {
        // Soundness guard: `(1,2)` and `(1,2)` are equal, so the noConfusion
        // builder must NOT manufacture a disequality proof for a true equality.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let lhs = prod_mk(
            nat_ty.clone(),
            nat_ty.clone(),
            Expr::nat_lit(1),
            Expr::nat_lit(2),
        );
        let rhs = prod_mk(nat_ty.clone(), nat_ty, Expr::nat_lit(1), Expr::nat_lit(2));
        let proof = build_noconfusion_ne_proof(
            &env,
            &prod_ty(
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            &lhs,
            &rhs,
            &Level::succ(Level::zero()),
        );
        assert!(
            proof.is_none(),
            "no disequality proof may exist for the true equality `(1,2) = (1,2)`"
        );
    }

    #[test]
    fn test_decide_eq_option_nat_equal_some_rejects_false_inequality() {
        // Soundness guard: `some 1 = some 1` is true, so no disequality proof.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let value = option_some(nat_ty.clone(), Expr::nat_lit(1));
        let proof = build_noconfusion_ne_proof(
            &env,
            &option_ty(nat_ty),
            &value,
            &value,
            &Level::succ(Level::zero()),
        );
        assert!(
            proof.is_none(),
            "no disequality proof may exist for the true equality `some 1 = some 1`"
        );
    }

    #[test]
    fn test_decidable_type_check_supports_sum_only_when_both_summands_decidable() {
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let undecidable_ty = Expr::const_(Name::from_string("A"), vec![]);

        assert!(
            decidable_type_check(&sum_ty(nat_ty.clone(), bool_ty.clone())),
            "Nat ⊕ Bool should reuse the decide_eq noConfusion lane"
        );
        assert!(
            !decidable_type_check(&sum_ty(nat_ty, undecidable_ty.clone())),
            "Nat ⊕ A should stay unsupported when one summand is unsupported"
        );
        assert!(
            !decidable_type_check(&sum_ty(undecidable_ty, bool_ty)),
            "A ⊕ Bool should stay unsupported when one summand is unsupported"
        );
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inl_reflexive_goal_closes() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let value = sum_inl(nat_ty.clone(), nat_ty, Expr::nat_lit(1));
        let goal = make_eq_goal(sty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive `inl 1 = inl 1` should close");
        assert!(state.is_complete(), "reflexive Sum.inl goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "reflexive Sum equality should stay trust-free"
        );
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inr_reflexive_goal_closes() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let value = sum_inr(nat_ty.clone(), nat_ty, Expr::nat_lit(2));
        let goal = make_eq_goal(sty, value.clone(), value);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("reflexive `inr 2 = inr 2` should close");
        assert!(state.is_complete(), "reflexive Sum.inr goal should close");
        assert_eq!(state.trusted_axiom_count(), 0);
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inl_vs_inr_inequality_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = sum_inl(nat_ty.clone(), nat_ty.clone(), Expr::nat_lit(1));
        let rhs = sum_inr(nat_ty.clone(), nat_ty, Expr::nat_lit(1));
        let goal = make_decidable_eq_goal(sty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`inl 1 ≠ inr 1` should close via Sum.noConfusion");
        assert!(state.is_complete(), "Sum inl/inr goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "Sum cross-constructor inequality should stay on the kernel proof path"
        );

        let proof = state
            .proof_term()
            .expect("completed Sum goal should retain the proof term");
        assert!(contains_named_const(&proof, "Sum.noConfusion"));
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inl_payload_differs_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = sum_inl(nat_ty.clone(), nat_ty.clone(), Expr::nat_lit(1));
        let rhs = sum_inl(nat_ty.clone(), nat_ty, Expr::nat_lit(2));
        let goal = make_decidable_eq_goal(sty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`inl 1 ≠ inl 2` should close via Sum.noConfusion");
        assert!(state.is_complete(), "Sum payload-differs goal should close");
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "Sum payload inequality should stay on the kernel proof path"
        );

        let proof = state
            .proof_term()
            .expect("completed Sum goal should retain the proof term");
        assert!(contains_named_const(&proof, "Sum.noConfusion"));
        assert!(contains_named_const(&proof, "Nat.noConfusion"));
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_inr_payload_differs_no_trusted_axioms() {
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let sty = sum_ty(nat_ty.clone(), nat_ty.clone());
        let lhs = sum_inr(nat_ty.clone(), nat_ty.clone(), Expr::nat_lit(1));
        let rhs = sum_inr(nat_ty.clone(), nat_ty, Expr::nat_lit(2));
        let goal = make_decidable_eq_goal(sty, lhs, rhs);
        let mut state = ProofState::new(env, goal);

        decide_eq(&mut state).expect("`inr 1 ≠ inr 2` should close via Sum.noConfusion");
        assert!(
            state.is_complete(),
            "Sum.inr payload-differs goal should close"
        );
        assert_eq!(state.trusted_axiom_count(), 0);

        let proof = state
            .proof_term()
            .expect("completed Sum goal should retain the proof term");
        assert!(contains_named_const(&proof, "Sum.noConfusion"));
        assert!(contains_named_const(&proof, "Nat.noConfusion"));
    }

    #[test]
    fn test_decide_eq_sum_nat_nat_equal_inl_rejects_false_inequality() {
        // Soundness guard: `inl 1 = inl 1` is true, so the noConfusion builder
        // must NOT manufacture a disequality proof for a true equality.
        let env = Environment::with_prelude();
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let value = sum_inl(nat_ty.clone(), nat_ty.clone(), Expr::nat_lit(1));
        let proof = build_noconfusion_ne_proof(
            &env,
            &sum_ty(nat_ty.clone(), nat_ty),
            &value,
            &value,
            &Level::succ(Level::zero()),
        );
        assert!(
            proof.is_none(),
            "no disequality proof may exist for the true equality `inl 1 = inl 1`"
        );
    }
}
