// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integer interval case splitting tactic (`interval_cases`).
//!
//! Extracted from `finite_cases.rs` for file-size compliance.
//!
//! The proof term is an interval DESCENT (see
//! [`super::interval_cases_proof`]), not an `Or.rec`/`Classical.em` chain:
//! every branch's equality hypothesis is bound by a real binder over a real
//! proof extracted from `Nat.lt_or_eq_of_le`, and the `n < lo` escape is
//! discharged against the caller's own lower bound. Nothing is assumed.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId, Level};

use super::finite_cases::make_nat_literal;
use super::interval_cases_proof::{build_interval_descent_proof, require_constants};
use super::nat_expr_eval::read_nat_numeral;
use super::{match_le, match_lt, Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Largest endpoint the tactic will materialize as a literal.
///
/// `make_int_literal` emits unary `Nat.succ` chains, so an interval such as
/// `1_000_000 ≤ n ≤ 1_000_002` would mint million-deep terms and type-check
/// them once per branch. The 100-value range cap does not bound the endpoint,
/// so bound it here. Fails closed with `InvalidTarget`.
const MAX_ENDPOINT: i64 = 1024;

/// Case split on an integer hypothesis within an interval.
///
/// Creates separate goals for each integer in [lower, upper] determined
/// from context bounds. Each sub-goal adds an equality hypothesis.
///
/// REQUIRES: `state` is a well-formed proof state
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal's context
///
/// ENSURES: on `Ok(())`, the original goal is closed via an interval-descent
/// `Or.rec` term and one sub-goal per integer value is prepended to
/// `state.goals`; each sub-goal's equality hypothesis is bound by a real
/// binder in that term
/// ENSURES: the range is capped at 100 values and endpoints at
/// [`MAX_ENDPOINT`]; larger ranges return `Err(InvalidTarget)`
/// ENSURES: on `Err(NoGoals)` or `Err(HypothesisNotFound)`, `state` is unchanged
/// ENSURES: on `Err(EnvironmentMissing)`, the ambient environment lacks a Nat
/// order lemma the descent cites; `state` is unchanged
pub fn interval_cases(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Try to determine bounds from context
    let bounds = find_integer_bounds(&goal, &hyp)?;
    let (lower, upper) = (bounds.lower.value, bounds.upper.value);

    // The descent is a Nat construction (`Nat.lt_or_eq_of_le`,
    // `Nat.le_of_succ_le_succ`, …). Other carriers are out of slice.
    if !is_nat_const(&hyp.ty) {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: "only Nat variables are supported".into(),
        });
    }

    if upper - lower > 100 {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!("range too large ({} values)", upper - lower + 1),
        });
    }

    if lower < 0 {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!("negative lower bound ({lower}) is not a Nat"),
        });
    }

    if upper > MAX_ENDPOINT {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!("endpoint {upper} exceeds the literal cap {MAX_ENDPOINT}"),
        });
    }

    // Fail closed BEFORE minting sub-goals: a minimal environment without Nat
    // order theory cannot type-check the descent, and a half-built state would
    // leave orphaned metavariables behind.
    require_constants(state)?;

    let (new_goals, value_exprs) =
        build_interval_goals(state, &goal, &hyp, hyp_name, lower, upper)?;

    // SOUNDNESS FIX (#2232, #2533): the descent links the original goal meta to
    // every sub-goal meta, and each sub-goal's `n_eq` is the BINDER of the
    // lambda holding that meta — derived, never assumed.
    let metas: Vec<_> = new_goals.iter().map(|g| g.meta_id).collect();
    let n_expr = Expr::fvar(hyp.fvar);
    let top_value = value_exprs
        .last()
        .cloned()
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: "empty interval".into(),
        })?;

    // A strict upper bound `n < upper+1` is `Nat.le (succ n) (succ upper)`;
    // peel one `succ` to get `n ≤ upper`. `make_int_literal` emits `Nat.succ`
    // chains, so `lit(upper+1) ≡ Nat.succ lit(upper)` syntactically. A bound
    // spelled as a source numeral (`@OfNat.ofNat Nat k inst`, which
    // `read_nat_numeral` reads) relates to that chain only DEFINITIONALLY;
    // `close_goal`'s kernel def-eq check below carries it, and fails closed
    // with `TypeMismatch` if it cannot.
    let h_upper = Expr::fvar(bounds.upper.fvar);
    let h_le_top = if bounds.upper.strict {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
            [n_expr.clone(), top_value, h_upper],
        )
    } else {
        h_upper
    };
    // A strict lower bound `lo-1 < n` is `Nat.le (succ (lo-1)) n` ≡ `lo ≤ n`,
    // so the hypothesis is passed through verbatim in both cases.
    let h_lower = Expr::fvar(bounds.lower.fvar);

    let proof = build_interval_descent_proof(
        &goal.target,
        &n_expr,
        &value_exprs,
        &metas,
        h_le_top,
        &h_lower,
    )?;

    // Part of #2154 Wave 10: migrated from close_goal_unchecked.
    // `close_goal` re-infers strictly and checks def-eq against the target, so
    // soundness never rests on `find_integer_bounds`' syntactic matching: a
    // mis-detected bound simply yields a `TypeMismatch`.
    state.close_goal(&goal, proof)?;

    for new_goal in new_goals.into_iter().rev() {
        state.goals.push_front(new_goal);
    }

    Ok(())
}

/// Build sub-goals for each integer value in the range [lower, upper].
///
/// Returns (goals, value_expressions) for proof construction, both in
/// ASCENDING value order.
///
/// # Binder-slot allocation (#2533)
///
/// The descent nests one `hlt` binder per value, outermost at the LARGEST
/// value, so value `k`'s equality binder sits at nesting position
/// `j = count-1-k`. `close_fvars` — and the `close_goal` scope guard mirroring
/// it — infer a tactic FVar's binder nesting depth from its offset above the
/// destination meta's binder base, so the binder at position `j` must have id
/// exactly `base + j`. GOAL-DERIVED minting supplies that base:
/// [`ProofState::goal_binder_base`] — the same capture-safe authority `intro`,
/// `by_cases`, `have` and `fin_cases` mint from — read ONCE, then advanced one
/// slot per nested binder, with the global cursor pushed past each allocation
/// so unrelated `fresh_fvar` calls cannot collide and `closed_proof`'s scan
/// still covers the ids. `fresh_fvar()` (the global cursor, which drifts past
/// the window whenever anything minted since the goal's meta was created) or
/// the historical `FVarId::new(ctx.len() + 1000)` land outside that window
/// entirely — the defect this rewrite removes.
///
/// REQUIRES: `lower <= upper` (caller enforces)
/// REQUIRES: `hyp` is a hypothesis from `goal.local_ctx`
///
/// ENSURES: returns `(goals, value_exprs)` where both vectors have length
/// `(upper - lower + 1)` and are ordered by ascending value
/// ENSURES: every sub-goal keeps the ORIGINAL target — the descent's `Or.rec`
/// motive is constant, so each minor premise must have type `goal.target`
/// exactly. (The old `substitute_fvar` branch only ever substituted into
/// targets that do not mention `hyp.fvar`, where it was the identity; keeping
/// the target is now unconditional rather than accidentally so.)
/// ENSURES: sub-goal `k`'s context is `goal.local_ctx` plus exactly one new
/// local `hyp_name_eq : hyp = valueₖ` at FVar id
/// `goal_binder_base(goal) + count-1-k` — EVERY branch, the last included,
/// because every branch's equality is bound by the descent
fn build_interval_goals(
    state: &mut ProofState,
    goal: &Goal,
    hyp: &LocalDecl,
    hyp_name: &clean_parser::SurfaceName,
    lower: i64,
    upper: i64,
) -> Result<(Vec<Goal>, Vec<Expr>), TacticError> {
    let value_exprs: Vec<Expr> = (lower..=upper).map(make_int_literal).collect();
    let eq_hyp_name = super::pattern::names::generated_suffix(hyp_name, "_eq");
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // GOAL-DERIVED minting: binder position `j` (outermost = largest value)
    // takes id `base + j` of the destination meta's positional window.
    let mut eq_fvar_id = state.goal_binder_base(goal);
    let mut new_goals = Vec::with_capacity(value_exprs.len());

    // Outermost binder (j = 0) belongs to the LARGEST value.
    for value_expr in value_exprs.iter().rev() {
        let eq_fvar = FVarId::new(eq_fvar_id);
        eq_fvar_id += 1;
        state.next_fvar = state.next_fvar.max(eq_fvar_id);

        // The sub-goal sees only its OWN equality, never the `hlt` binders the
        // descent stacks above it (those are machinery, and omitting them is a
        // `clear`, which the goal-scope guard permits).
        let mut new_ctx = goal.local_ctx.clone();
        new_ctx.push(LocalDecl {
            binder_info: Default::default(),
            fvar: eq_fvar,
            name: eq_hyp_name.clone(),
            ty: make_equality_type(
                &nat_ty,
                &Expr::fvar(hyp.fvar),
                value_expr,
                Level::succ(Level::zero()), // Nat : Type 0 = Sort 1
            ),
            value: None,
        });

        let new_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
        new_goals.push(Goal {
            meta_id: new_meta_id,
            target: goal.target.clone(),
            local_ctx: new_ctx,
            case_binders: goal.case_binders.clone(),
            tag: None,
        });
    }

    // Built outermost-first (descending value); report in ascending order.
    new_goals.reverse();

    Ok((new_goals, value_exprs))
}

/// One endpoint of a detected interval, with the hypothesis that witnesses it.
#[derive(Clone, Copy)]
struct IntervalBound {
    /// The (already normalized) inclusive Nat endpoint.
    value: i64,
    /// The context hypothesis proving it.
    fvar: FVarId,
    /// `true` when the hypothesis is `<` rather than `≤`.
    strict: bool,
}

/// A detected inclusive interval `lower.value ≤ n ≤ upper.value`.
struct IntervalBounds {
    lower: IntervalBound,
    upper: IntervalBound,
}

/// Take `candidate` as the new lower bound when it is strictly tighter.
///
/// Strict improvement (not `>=`) keeps the chosen witness independent of
/// context order when a literal bound is duplicated.
fn tighten_lower(slot: &mut Option<IntervalBound>, candidate: IntervalBound) {
    if slot.is_none_or(|cur| candidate.value > cur.value) {
        *slot = Some(candidate);
    }
}

/// Take `candidate` as the new upper bound when it is strictly tighter.
fn tighten_upper(slot: &mut Option<IntervalBound>, candidate: IntervalBound) {
    if slot.is_none_or(|cur| candidate.value < cur.value) {
        *slot = Some(candidate);
    }
}

/// `Const("Nat", [])`?
fn is_nat_const(expr: &Expr) -> bool {
    matches!(expr.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

/// Is `expr` exactly `FVar(fvar)`?
fn is_fvar(expr: &Expr, fvar: FVarId) -> bool {
    matches!(expr.kind(), ExprKind::FVar(id) if *id == fvar)
}

/// Find integer bounds for a variable from the context
///
/// The bound PROOFS are load-bearing now (the descent applies them to
/// `Nat.lt_or_eq_of_le` / `Nat.le_trans`), so both the carrier and the
/// witnessing hypothesis are recorded, and non-`Nat` carriers are skipped.
/// `match_le` / `match_lt` are purely syntactic head-name matches, so this is
/// the only place the carrier is checked.
///
/// REQUIRES: `hyp` is a hypothesis from `goal.local_ctx`
///
/// ENSURES: on `Ok(bounds)`, `bounds.lower.value <= bounds.upper.value` and
/// both bounds were derived from Nat-carrier `≤` or `<` hypotheses in the goal
/// context, each paired with the FVar of the hypothesis proving it
/// ENSURES: returns `Err(InvalidTarget)` when no lower bound, no upper bound,
/// or inconsistent bounds are found (#2239 soundness fix)
fn find_integer_bounds(goal: &Goal, hyp: &LocalDecl) -> Result<IntervalBounds, TacticError> {
    let mut lower: Option<IntervalBound> = None;
    let mut upper: Option<IntervalBound> = None;

    // Look through hypotheses for bounds
    for decl in &goal.local_ctx {
        // Check for lhs ≤ rhs patterns
        if let Some((ty, lhs, rhs)) = match_le(&decl.ty) {
            if is_nat_const(&ty) {
                // `v ≤ n` — lower bound
                if is_fvar(&rhs, hyp.fvar) {
                    if let Some(value) = expr_to_int(&lhs) {
                        tighten_lower(
                            &mut lower,
                            IntervalBound {
                                value,
                                fvar: decl.fvar,
                                strict: false,
                            },
                        );
                    }
                }
                // `n ≤ v` — upper bound
                if is_fvar(&lhs, hyp.fvar) {
                    if let Some(value) = expr_to_int(&rhs) {
                        tighten_upper(
                            &mut upper,
                            IntervalBound {
                                value,
                                fvar: decl.fvar,
                                strict: false,
                            },
                        );
                    }
                }
            }
        }

        // Check for lhs < rhs patterns
        if let Some((ty, lhs, rhs)) = match_lt(&decl.ty) {
            if is_nat_const(&ty) {
                // `v < n` — lower bound `v + 1 ≤ n`
                if is_fvar(&rhs, hyp.fvar) {
                    if let Some(value) = expr_to_int(&lhs).and_then(|v| v.checked_add(1)) {
                        tighten_lower(
                            &mut lower,
                            IntervalBound {
                                value,
                                fvar: decl.fvar,
                                strict: true,
                            },
                        );
                    }
                }
                // `n < v` — upper bound `n ≤ v - 1`
                if is_fvar(&lhs, hyp.fvar) {
                    if let Some(value) = expr_to_int(&rhs).and_then(|v| v.checked_sub(1)) {
                        tighten_upper(
                            &mut upper,
                            IntervalBound {
                                value,
                                fvar: decl.fvar,
                                strict: true,
                            },
                        );
                    }
                }
            }
        }
    }

    // SOUNDNESS FIX (#2239): Return error when no bounds found.
    // Previously fabricated default bounds (0..10), unsound for unbounded integers.
    let (lower, upper) = match (lower, upper) {
        (Some(lower), Some(upper)) => (lower, upper),
        (found_lower, found_upper) => {
            let missing = match (found_lower.is_none(), found_upper.is_none()) {
                (true, true) => "no bounds",
                (true, false) => "no lower bound",
                _ => "no upper bound",
            };
            return Err(TacticError::InvalidTarget {
                tactic: "interval_cases".into(),
                detail: format!("{missing} found in context; add ≤ or < hypotheses"),
            });
        }
    };

    if lower.value > upper.value {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: "inconsistent bounds".into(),
        });
    }

    Ok(IntervalBounds { lower, upper })
}

/// Convert expression to integer if possible
///
/// Delegates to the shared `nat_expr_eval::read_nat_numeral` reader so the
/// `@OfNat.ofNat Nat k inst` form the elaborator builds for a source numeral is
/// recognized. Before that (RC-H), this handled only `Nat.zero` / a `Nat.succ`
/// chain / a raw `Lit(Nat)`, so `interval_cases n` under `h1 : 2 ≤ n` and
/// `h2 : n ≤ 3` reported "no bounds found in context" while the
/// `Nat.succ`-spelled bounds were read.
///
/// REQUIRES: `expr` is a well-formed Lean expression
///
/// ENSURES: returns `Some(n)` when `expr` denotes the Nat numeral `n` and `n`
/// fits in an `i64`
/// ENSURES: returns `None` for non-numeral expressions
/// ENSURES: recursive descent runs under `stack_safe`
pub(crate) fn expr_to_int(expr: &Expr) -> Option<i64> {
    read_nat_numeral(expr).and_then(|v| i64::try_from(v).ok())
}

/// Make an integer literal expression
///
/// ENSURES: for `n >= 0`, delegates to `make_nat_literal` (a `Nat.succ` chain —
/// the descent in [`super::interval_cases_proof`] relies on
/// `lit(k+1) ≡ Nat.succ lit(k)` syntactically)
/// ENSURES: for `n < 0`, returns `Int.negOfNat(|n|)`
pub(crate) fn make_int_literal(n: i64) -> Expr {
    if n >= 0 {
        make_nat_literal(n as u64)
    } else {
        // For negative, use Int.negOfNat
        Expr::app(
            Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            make_nat_literal(n.unsigned_abs()),
        )
    }
}

/// Make an equality type expression: `@Eq ty lhs rhs`
///
/// REQUIRES: `ty`, `lhs`, `rhs` are well-formed and `lhs`/`rhs` inhabit `ty`
///
/// ENSURES: returns the fully-applied `@Eq.{level} ty lhs rhs` expression
pub(crate) fn make_equality_type(ty: &Expr, lhs: &Expr, rhs: &Expr, level: Level) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![level]);
    Expr::app(
        Expr::app(Expr::app(eq, ty.clone()), lhs.clone()),
        rhs.clone(),
    )
}
