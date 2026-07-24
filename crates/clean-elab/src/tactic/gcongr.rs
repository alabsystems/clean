// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalized congruence tactic for inequalities
//!
//! Provides the `gcongr` tactic which proves goals of the form
//! `f a₁ ... aₙ ≤ f b₁ ... bₙ` by creating subgoals `aᵢ ≤ bᵢ`
//! for arguments that differ.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::unify::MetaState;

use super::tc_app;
use super::{Goal, ProofState, TacticError, TacticResult};

/// Generalized congruence tactic for inequalities.
///
/// `gcongr` proves goals of the form `f a₁ ... aₙ ≤ f b₁ ... bₙ` by creating
/// subgoals `aᵢ ≤ bᵢ` for arguments that differ. It's particularly useful for:
/// - Monotonic functions (add, mul for non-negative)
/// - Norm bounds
/// - Integral bounds
///
/// The tactic handles:
/// - `≤` (Le), `<` (Lt), `≥` (Ge), `>` (Gt)
/// - Arithmetic operations with monotonicity
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, the current goal is a recognized inequality accepted
///   by [`match_inequality`].
/// ENSURES: On `Ok(())`, either closes a reflexive non-strict inequality or
///   replaces the goal with congruence subgoals via [`gcongr_inequality`].
/// ENSURES: Returns `Err(GoalMismatch)` for non-inequality goals and
///   `Err(SearchExhausted)` when no supported monotonicity rule applies.
pub fn gcongr(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Try to match an inequality
    if let Some((rel, ty, inst, lhs, rhs)) = match_inequality(&target) {
        return gcongr_inequality(state, &goal, rel, &ty, &inst, &lhs, &rhs);
    }

    Err(TacticError::GoalMismatch(
        "gcongr: goal must be an inequality".to_string(),
    ))
}

/// Inequality relation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IneqRel {
    Le, // ≤
    Lt, // <
    Ge, // ≥
    Gt, // >
}

/// Match inequality patterns.
///
/// Returns `(rel, type, instance, lhs, rhs)`. For well-formed expressions like
/// `@LE.le.{0} Nat instLENat a b`, extracts all 4 args. For legacy 2-arg forms
/// like `LE.le a b`, defaults type to `Nat` and instance to the appropriate
/// Nat instance.
///
/// Part of #2078: also extracts instance arg (previously discarded).
///
/// REQUIRES: `expr` is a well-formed application spine.
/// ENSURES: Returns `Some(...)` only for recognized `LE`/`LT`/`GE`/`GT`
///   constants (including legacy aliases).
/// ENSURES: Legacy 2-arg and 3-arg forms are normalized by synthesizing the
///   missing Nat type and/or default relation instance.
pub(crate) fn match_inequality(expr: &Expr) -> Option<(IneqRel, Expr, Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        let name_str = name.to_string();

        let (rel, default_inst_name) =
            if name_str == "LE.le" || name_str == "HasLe.le" || name_str == "le" {
                (IneqRel::Le, "instLENat")
            } else if name_str == "LT.lt" || name_str == "HasLt.lt" || name_str == "lt" {
                (IneqRel::Lt, "instLTNat")
            } else if name_str == "GE.ge" || name_str == "HasGe.ge" || name_str == "ge" {
                // GE.ge takes an LE instance (GE is defined via LE)
                (IneqRel::Ge, "instLENat")
            } else if name_str == "GT.gt" || name_str == "HasGt.gt" || name_str == "gt" {
                // GT.gt takes an LT instance (GT is defined via LT)
                (IneqRel::Gt, "instLTNat")
            } else {
                return None;
            };

        if args.len() < 2 {
            return None;
        }

        // Extract type and instance based on arity:
        // 4 args: @Rel α inst lhs rhs (fully applied)
        // 3 args: @Rel α lhs rhs (missing instance)
        // 2 args: Rel lhs rhs (missing type and instance — legacy)
        let (ty, inst, lhs, rhs) = if args.len() >= 4 {
            (
                args[0].clone(),
                args[1].clone(),
                args[args.len() - 2].clone(),
                args[args.len() - 1].clone(),
            )
        } else if args.len() == 3 {
            (
                args[0].clone(),
                Expr::const_(Name::from_string(default_inst_name), vec![]),
                args[1].clone(),
                args[2].clone(),
            )
        } else {
            (
                tc_app::nat_type(),
                Expr::const_(Name::from_string(default_inst_name), vec![]),
                args[0].clone(),
                args[1].clone(),
            )
        };

        return Some((rel, ty, inst, lhs, rhs));
    }
    None
}

/// Handle inequality goal with gcongr.
///
/// Part of #2154 goal-decomposition pattern: reflexivity case uses close_goal
/// (checked). General decomposition delegates to gcongr_monotonic which builds
/// a composite proof with mvar subgoal references.
fn gcongr_inequality(
    state: &mut ProofState,
    goal: &Goal,
    rel: IneqRel,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> TacticResult {
    // Check if both sides have the same head (function application)
    let lhs_head = lhs.get_app_fn();
    let rhs_head = rhs.get_app_fn();

    // Use goal's local context for def-eq checks so FVars resolve correctly.
    // Part of #2212: TypeChecker::with_mode creates empty local context.
    if state.is_def_eq(goal, lhs_head, rhs_head) {
        let lhs_args = lhs.get_app_args();
        let rhs_args = rhs.get_app_args();

        if lhs_args.len() == rhs_args.len() {
            // Find differing argument indices
            let differing: Vec<usize> = lhs_args
                .iter()
                .zip(rhs_args.iter())
                .enumerate()
                .filter(|(_, (l, r))| !state.is_def_eq(goal, l, r))
                .map(|(i, _)| i)
                .collect();

            if differing.is_empty() {
                // All args equal, close with reflexivity via close_goal (checked).
                // Part of #2154: previously used metas.assign (bypassed type check).
                let refl_proof = match rel {
                    IneqRel::Le | IneqRel::Ge => {
                        // Generic reflexivity: look up {Type}.le_refl in the
                        // environment. Works for Nat, Int, Real, Rat, or any
                        // type with a registered le_refl axiom.
                        // Part of #2075: previously hardcoded Nat.le_refl,
                        // producing ill-typed proofs for non-Nat types.
                        let type_name = match ty.kind() {
                            ExprKind::Const(name, _) => name.to_string(),
                            _ => {
                                return Err(TacticError::InvalidTarget {
                                    tactic: "gcongr".into(),
                                    detail: "reflexivity requires a named type constant".into(),
                                });
                            }
                        };
                        let le_refl_name = Name::from_string(&format!("{type_name}.le_refl"));
                        if state.env().get_const(&le_refl_name).is_none() {
                            return Err(TacticError::EnvironmentMissing {
                                constant: format!("{type_name}.le_refl"),
                            });
                        }
                        Expr::app(Expr::const_(le_refl_name, vec![]), lhs.clone())
                    }
                    IneqRel::Lt | IneqRel::Gt => {
                        return Err(TacticError::InvalidTarget {
                            tactic: "gcongr".into(),
                            detail: "strict inequality cannot hold for equal terms".into(),
                        });
                    }
                };
                return state.close_goal(goal, refl_proof);
            }

            // General function decomposition with differing args requires
            // function-specific monotonicity lemmas (@[gcongr] database).
            // Delegate to gcongr_monotonic for known operations (addition).
            // Fall through to gcongr_monotonic below.
        }
    }

    // Try monotonicity rules for specific operations (addition)
    gcongr_monotonic(state, goal, rel, ty, inst, lhs, rhs)
}

/// Create inequality goal expression with proper typeclass implicit args.
///
/// Builds `@Rel.{u} ty inst lhs rhs` — the fully-applied form required by the kernel.
/// Part of #2078: previously only produced `Rel lhs rhs` (missing type + instance).
///
/// REQUIRES: `rel`, `ty`, `inst`, `lhs`, and `rhs` form a compatible relation
///   application; `state` can construct the relation constant.
/// ENSURES: Returns a fully-applied inequality expression with explicit type and
///   instance arguments.
/// ENSURES: Operand order is preserved as `lhs` then `rhs`.
pub(crate) fn make_ineq_goal(
    rel: IneqRel,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    state: &mut ProofState,
) -> Expr {
    let rel_name = match rel {
        IneqRel::Le => "LE.le",
        IneqRel::Lt => "LT.lt",
        IneqRel::Ge => "GE.ge",
        IneqRel::Gt => "GT.gt",
    };
    tc_app::mk_tc_rel(
        state.mk_const_str(rel_name),
        ty.clone(),
        inst.clone(),
        lhs.clone(),
        rhs.clone(),
    )
}

/// Try monotonicity rules for arithmetic operations.
///
/// Part of #2154 goal-decomposition pattern: builds a composite proof using
/// Nat.add_le_add / Nat.add_lt_add with mvar subgoal references, then closes
/// the original goal via close_goal (checked).
fn gcongr_monotonic(
    state: &mut ProofState,
    goal: &Goal,
    rel: IneqRel,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> TacticResult {
    // Match addition: a + b ≤ c + d
    if let (Some((a, b)), Some((c, d))) = (match_add(lhs), match_add(rhs)) {
        // Select monotonicity lemma:
        //   Le/Ge → Nat.add_le_add : ∀ a b c d, Nat.le a b → Nat.le c d → Nat.le (a+c) (b+d)
        //   Lt/Gt → Nat.add_lt_add : ∀ a b c d, Nat.lt a b → Nat.lt c d → Nat.lt (a+c) (b+d)
        let lemma_name_str = match rel {
            IneqRel::Le | IneqRel::Ge => "Nat.add_le_add",
            IneqRel::Lt | IneqRel::Gt => "Nat.add_lt_add",
        };
        let lemma_name = Name::from_string(lemma_name_str);
        if state.env().get_const(&lemma_name).is_none() {
            return Err(TacticError::EnvironmentMissing {
                constant: lemma_name_str.to_string(),
            });
        }

        // Part of #2075: normalize Ge/Gt subgoals to LE/LT equivalents.
        // GE.ge a b ≡ LE.le b a at kernel level, so create LE.le subgoals
        // with swapped arguments for robustness. Use the extracted type (not
        // hardcoded Nat) and the corresponding LE/LT instance.
        let (sub_rel, sub_inst) = match rel {
            IneqRel::Le | IneqRel::Lt => (rel, inst.clone()),
            IneqRel::Ge => (IneqRel::Le, inst.clone()), // GE uses LE instance
            IneqRel::Gt => (IneqRel::Lt, inst.clone()), // GT uses LT instance
        };
        // Create subgoal targets with normalized relation and swapped args for Ge/Gt
        let (g1_lhs, g1_rhs, g2_lhs, g2_rhs) = match rel {
            IneqRel::Le | IneqRel::Lt => (a.clone(), c.clone(), b.clone(), d.clone()),
            IneqRel::Ge | IneqRel::Gt => (c.clone(), a.clone(), d.clone(), b.clone()),
        };
        let goal1 = make_ineq_goal(sub_rel, ty, &sub_inst, &g1_lhs, &g1_rhs, state);
        let goal2 = make_ineq_goal(sub_rel, ty, &sub_inst, &g2_lhs, &g2_rhs, state);

        // Create fresh metas for subgoals
        let meta1 = state.fresh_meta(goal1.clone());
        let meta1_expr = Expr::fvar(MetaState::to_fvar(meta1));
        let meta2 = state.fresh_meta(goal2.clone());
        let meta2_expr = Expr::fvar(MetaState::to_fvar(meta2));

        // Build composite proof: Nat.add_le_add p1 p2 p3 p4 h1 h2
        //
        // Lemma signature: ∀ a' b' c' d', le a' b' → le c' d' → le (a'+c') (b'+d')
        // Subgoals are already normalized to LE/LT with correct arg order
        // (Ge/Gt were swapped above), so parameters match directly.
        let (p1, p2, p3, p4) = (g1_lhs, g1_rhs, g2_lhs, g2_rhs);

        let lemma = Expr::const_(lemma_name, vec![]);
        let mut proof = lemma;
        proof = Expr::app(proof, p1);
        proof = Expr::app(proof, p2);
        proof = Expr::app(proof, p3);
        proof = Expr::app(proof, p4);
        proof = Expr::app(proof, meta1_expr);
        proof = Expr::app(proof, meta2_expr);

        // Close original goal with composite proof (assigns meta + pops goal).
        state.close_goal(goal, proof)?;

        // Push subgoals (goal2 first so goal1 is at front)
        state.goals.insert(
            0,
            Goal {
                meta_id: meta2,
                target: goal2,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            },
        );
        state.goals.insert(
            0,
            Goal {
                meta_id: meta1,
                target: goal1,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            },
        );

        return Ok(());
    }

    // Match multiplication: a * c ≤ b * d
    if let (Some((a, c)), Some((b, d))) = (match_mul(lhs), match_mul(rhs)) {
        return gcongr_mul(state, goal, rel, ty, inst, &a, &c, &b, &d);
    }

    Err(TacticError::SearchExhausted {
        tactic: "gcongr".into(),
        detail: "cannot apply congruence rules (only addition and multiplication monotonicity \
             are currently supported)"
            .into(),
    })
}

/// Handle multiplication monotonicity: prove `a*c ≤ b*d` from `a ≤ b` and `c ≤ d`.
///
/// Decomposes the operands of `lhs = a*c` and `rhs = b*d`:
/// - **Nat** uses the constructive `Nat.mul_le_mul a b c d h1 h2`. When one
///   factor is shared (def-eq) it prefers the one-sided `Nat.mul_le_mul_left`
///   (`c*a ≤ c*b`, shared left) / `Nat.mul_le_mul_right` (`a*c ≤ b*c`, shared
///   right) so only the genuinely differing factor produces a subgoal.
/// - **Int** uses the one-sided `Int.mul_le_mul_of_nonneg_left a b c h_ab h_c`
///   (`c*a ≤ c*b`) and is applied only when the left factor is shared; the
///   `0 ≤ c` nonneg side condition is emitted as an additional subgoal so the
///   proof term stays kernel-checked. Other Int shapes leave the goal.
///
/// `Lt`/`Gt` multiplication is not handled (no constructive strict-mul lemma is
/// wired here); those fall through to `SearchExhausted`. `Ge`/`Gt` are
/// normalized to `Le`/`Lt` with swapped operands, mirroring the addition branch.
#[allow(clippy::too_many_arguments)]
fn gcongr_mul(
    state: &mut ProofState,
    goal: &Goal,
    rel: IneqRel,
    ty: &Expr,
    inst: &Expr,
    a: &Expr,
    c: &Expr,
    b: &Expr,
    d: &Expr,
) -> TacticResult {
    // Normalize Ge → Le with swapped operands (a*c ≥ b*d ≡ b*d ≤ a*c).
    // Strict (Lt/Gt) multiplication is not supported here.
    let (la, lc, ra, rc) = match rel {
        IneqRel::Le => (a.clone(), c.clone(), b.clone(), d.clone()),
        IneqRel::Ge => (b.clone(), d.clone(), a.clone(), c.clone()),
        IneqRel::Lt | IneqRel::Gt => {
            return Err(TacticError::SearchExhausted {
                tactic: "gcongr".into(),
                detail: "strict multiplication monotonicity is not supported".into(),
            });
        }
    };

    // From here the (normalized) goal is `la*lc ≤ ra*rc`.
    let type_name = match ty.kind() {
        ExprKind::Const(name, _) => name.to_string(),
        _ => {
            return Err(TacticError::SearchExhausted {
                tactic: "gcongr".into(),
                detail: "multiplication monotonicity requires a named type".into(),
            });
        }
    };

    match type_name.as_str() {
        "Nat" => gcongr_mul_nat(state, goal, inst, &la, &lc, &ra, &rc),
        "Int" => gcongr_mul_int(state, goal, &la, &lc, &ra, &rc),
        _ => Err(TacticError::SearchExhausted {
            tactic: "gcongr".into(),
            detail: format!("multiplication monotonicity unsupported for type {type_name}"),
        }),
    }
}

/// Nat multiplication monotonicity for `la*lc ≤ ra*rc`.
///
/// Prefers the one-sided constructive lemmas when a factor is shared:
/// - `la` def-eq `ra` → `Nat.mul_le_mul_left la lc rc h (h : lc ≤ rc)`.
/// - `lc` def-eq `rc` → `Nat.mul_le_mul_right la ra lc h (h : la ≤ ra)`.
/// - otherwise → `Nat.mul_le_mul la ra lc rc h1 h2` (two subgoals).
fn gcongr_mul_nat(
    state: &mut ProofState,
    goal: &Goal,
    inst: &Expr,
    la: &Expr,
    lc: &Expr,
    ra: &Expr,
    rc: &Expr,
) -> TacticResult {
    let nat_ty = tc_app::nat_type();
    let left_shared = state.is_def_eq(goal, la, ra);
    let right_shared = state.is_def_eq(goal, lc, rc);

    if left_shared && !right_shared {
        // Nat.mul_le_mul_left : ∀ a b c, a ≤ b → (c*a) ≤ (c*b)
        // Here c = la (= ra), a = lc, b = rc; subgoal `lc ≤ rc`.
        let lemma = require_const(state, "Nat.mul_le_mul_left")?;
        let sub = make_ineq_goal(IneqRel::Le, &nat_ty, inst, lc, rc, state);
        let meta = state.fresh_meta(sub.clone());
        let meta_expr = Expr::fvar(MetaState::to_fvar(meta));
        // Nat.mul_le_mul_left a b c h  with a=lc, b=rc, c=la
        let proof = Expr::apps(lemma, [lc.clone(), rc.clone(), la.clone(), meta_expr]);
        state.close_goal(goal, proof)?;
        state.goals.insert(
            0,
            Goal {
                meta_id: meta,
                target: sub,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            },
        );
        return Ok(());
    }

    if right_shared && !left_shared {
        // Nat.mul_le_mul_right : ∀ a b c, a ≤ b → (a*c) ≤ (b*c)
        // Here c = lc (= rc), a = la, b = ra; subgoal `la ≤ ra`.
        let lemma = require_const(state, "Nat.mul_le_mul_right")?;
        let sub = make_ineq_goal(IneqRel::Le, &nat_ty, inst, la, ra, state);
        let meta = state.fresh_meta(sub.clone());
        let meta_expr = Expr::fvar(MetaState::to_fvar(meta));
        // Nat.mul_le_mul_right a b c h  with a=la, b=ra, c=lc
        let proof = Expr::apps(lemma, [la.clone(), ra.clone(), lc.clone(), meta_expr]);
        state.close_goal(goal, proof)?;
        state.goals.insert(
            0,
            Goal {
                meta_id: meta,
                target: sub,
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            },
        );
        return Ok(());
    }

    // General two-sided. Lean's real `Nat.mul_le_mul` binds `{n₁ m₁ n₂ m₂}`
    // with `(h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂)`, concluding `n₁*m₁ ≤ n₂*m₂`. The
    // goal here is `la*lc ≤ ra*rc`, so instantiate
    // `n₁ := la, m₁ := lc, n₂ := ra, m₂ := rc` — the explicit-arg spine is
    // `[la, lc, ra, rc, h₁, h₂]` with subgoals `la ≤ ra` (h₁) and `lc ≤ rc`
    // (h₂). (An earlier transposed spine `[la, ra, lc, rc, …]` matched the
    // former transposed prelude type; see
    // `nat_arith_order_proof::register_nat_mul_le_mul`.)
    let lemma = require_const(state, "Nat.mul_le_mul")?;
    let goal1 = make_ineq_goal(IneqRel::Le, &nat_ty, inst, la, ra, state);
    let goal2 = make_ineq_goal(IneqRel::Le, &nat_ty, inst, lc, rc, state);
    let meta1 = state.fresh_meta(goal1.clone());
    let meta1_expr = Expr::fvar(MetaState::to_fvar(meta1));
    let meta2 = state.fresh_meta(goal2.clone());
    let meta2_expr = Expr::fvar(MetaState::to_fvar(meta2));
    let proof = Expr::apps(
        lemma,
        [
            la.clone(),
            lc.clone(),
            ra.clone(),
            rc.clone(),
            meta1_expr,
            meta2_expr,
        ],
    );
    state.close_goal(goal, proof)?;
    state.goals.insert(
        0,
        Goal {
            meta_id: meta2,
            target: goal2,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        },
    );
    state.goals.insert(
        0,
        Goal {
            meta_id: meta1,
            target: goal1,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        },
    );
    Ok(())
}

/// Int multiplication monotonicity for `la*lc ≤ ra*rc`.
///
/// Only the shared-left-factor case `c*a ≤ c*b` is sound here: it discharges via
/// `Int.mul_le_mul_of_nonneg_left a b c (h_ab : a ≤ b) (h_c : 0 ≤ c)`. The two
/// subgoals — the monotonicity premise `lc ≤ rc` and the nonneg side condition
/// `0 ≤ c` — are emitted, keeping the closing proof term kernel-checked. Any
/// other Int shape (no shared factor) leaves the goal untouched.
fn gcongr_mul_int(
    state: &mut ProofState,
    goal: &Goal,
    la: &Expr,
    lc: &Expr,
    ra: &Expr,
    rc: &Expr,
) -> TacticResult {
    if !state.is_def_eq(goal, la, ra) {
        return Err(TacticError::SearchExhausted {
            tactic: "gcongr".into(),
            detail: "Int multiplication monotonicity requires a shared left factor".into(),
        });
    }
    // Shared left factor c = la (= ra); goal is `c*lc ≤ c*rc`.
    // Int.mul_le_mul_of_nonneg_left : ∀ a b c, a ≤ b → 0 ≤ c → (c*a) ≤ (c*b)
    // with a = lc, b = rc, c = la.
    let lemma = require_const(state, "Int.mul_le_mul_of_nonneg_left")?;
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let int_inst = Expr::const_(Name::from_string("instLEInt"), vec![]);

    // Subgoal 1: lc ≤ rc.
    let mono_goal = make_ineq_goal(IneqRel::Le, &int_ty, &int_inst, lc, rc, state);
    // Subgoal 2: 0 ≤ c  (nonneg side condition; 0 ≡ Int.ofNat Nat.zero).
    let int_zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nonneg_goal = make_ineq_goal(IneqRel::Le, &int_ty, &int_inst, &int_zero, la, state);

    let mono_meta = state.fresh_meta(mono_goal.clone());
    let mono_expr = Expr::fvar(MetaState::to_fvar(mono_meta));
    let nonneg_meta = state.fresh_meta(nonneg_goal.clone());
    let nonneg_expr = Expr::fvar(MetaState::to_fvar(nonneg_meta));

    let proof = Expr::apps(
        lemma,
        [lc.clone(), rc.clone(), la.clone(), mono_expr, nonneg_expr],
    );
    state.close_goal(goal, proof)?;
    state.goals.insert(
        0,
        Goal {
            meta_id: nonneg_meta,
            target: nonneg_goal,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        },
    );
    state.goals.insert(
        0,
        Goal {
            meta_id: mono_meta,
            target: mono_goal,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        },
    );
    Ok(())
}

/// Look up a required closing lemma constant, erroring if absent from the env.
fn require_const(state: &ProofState, name: &str) -> Result<Expr, TacticError> {
    let cname = Name::from_string(name);
    if state.env().get_const(&cname).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: name.to_string(),
        });
    }
    Ok(Expr::const_(cname, vec![]))
}

/// Match addition pattern a + b
///
/// REQUIRES: `expr` is a well-formed application spine.
/// ENSURES: Returns `Some((a, b))` only for recognized addition heads
///   (`HAdd.hAdd`, `Add.add`, `Nat.add`, `Int.add`) with two explicit operands.
/// ENSURES: Exact-name matching avoids false positives from unrelated constants.
pub(crate) fn match_add(expr: &Expr) -> Option<(Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        let name_str = name.to_string();
        // Part of #2075: use exact name matching instead of contains("add")
        // which falsely matches "addr", "padding", "ReadAddr", etc.
        if matches!(
            name_str.as_str(),
            "HAdd.hAdd" | "Add.add" | "Nat.add" | "Int.add"
        ) && args.len() >= 2
        {
            return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
        }
    }

    // Check for deeper application (HAdd.hAdd α β γ inst a b)
    if let ExprKind::App(f, b) = expr.kind() {
        if let ExprKind::App(f2, a) = f.kind() {
            let inner_head = f2.get_app_fn();
            if let ExprKind::Const(name, _) = inner_head.kind() {
                if name.to_string() == "HAdd.hAdd" {
                    return Some((a.as_ref().clone(), b.as_ref().clone()));
                }
            }
        }
    }

    None
}

/// Match multiplication pattern a * b.
///
/// Mirror of [`match_add`] for the multiplicative operators. The last two
/// explicit arguments are the operands, so it works for both the homogeneous
/// `Nat.mul a b` / `Int.mul a b` forms and the heterogeneous
/// `@HMul.hMul α β γ inst a b` form (where the trailing two args are still the
/// operands).
///
/// REQUIRES: `expr` is a well-formed application spine.
/// ENSURES: Returns `Some((a, b))` only for recognized multiplication heads
///   (`HMul.hMul`, `Mul.mul`, `Nat.mul`, `Int.mul`) with two explicit operands.
/// ENSURES: Exact-name matching avoids false positives from unrelated constants.
pub(crate) fn match_mul(expr: &Expr) -> Option<(Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        let name_str = name.to_string();
        // Exact name matching (consistent with match_add): avoids false
        // positives such as "mult", "Multiset", "cumulative", etc.
        if matches!(
            name_str.as_str(),
            "HMul.hMul" | "Mul.mul" | "Nat.mul" | "Int.mul"
        ) && args.len() >= 2
        {
            return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
        }
    }

    None
}
