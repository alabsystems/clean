// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE level-equation solver (U2 rung 3a).
//!
//! Exactly one arm set survives: both `unify_levels` entry points — the
//! primary `Unifier` (unify/unifier/mod.rs) and the `unify_ext`
//! secondary — delegate here, retiring the measured divergence between
//! them (the secondary lacked rigid-preference, Miller Max/IMax slices,
//! and occurs-checks; see the U2 ladder doc, rung 2/3 bullets).
//!
//! Arms, in order:
//! 1. instantiate + syntactic equality
//! 2. param =?= param (rigid-preserving assignment direction)
//! 3. param =?= concrete (either side)
//! 4. Succ =?= Succ decomposition (recursive, so whole Succ towers cancel)
//! 5. param =?= Succ(..) with occurs-check (either side)
//! 6. param =?= Max/IMax (Miller slice, occurs-checked, either side)
//! 7. Max(a,b) =?= Zero → a = 0 ∧ b = 0 (most-general, rung 3)
//! 8. IMax(a,b) =?= Zero → b = 0 (most-general: imax _ 0 = 0, and b > 0
//!    forces imax = max ≥ b > 0; rung 3)
//! 9. conservative fallthrough: normalized `is_def_eq`, else Failure
//!    (with the rung-0b histogram classifier on the failure path)
//!
//! Every assignment funnels through `MetaState::add_level_constraint`,
//! which refuses rigid targets — so a wrong arm cannot silently
//! monomorphize a declared `.{u}` — and the assembled term is always
//! kernel-rechecked downstream.

use clean_kernel::name::Name;
use clean_kernel::Level;

use super::meta_state::MetaState;
use super::unifier::UnifyResult;
use crate::stack_safe;

/// Level occurs-check: does the parameter `name` appear anywhere in `level`?
pub(crate) fn level_param_occurs(name: &Name, level: &Level) -> bool {
    let mut params = Vec::new();
    level.collect_params(&mut params);
    params.iter().any(|p| p == name)
}

fn assign(metas: &mut MetaState, name: Name, level: Level) -> UnifyResult {
    match metas.add_level_constraint(name, level) {
        Ok(()) => UnifyResult::Success,
        Err(message) => UnifyResult::Failure(message),
    }
}

/// Solve `l1 =?= l2`, assigning level metavariables in `metas`.
///
/// An UNDETERMINED equation (some side still mentions a solvable, non-rigid
/// level parameter) is DEFERRED rather than failed — see arm 9. Deferral is not
/// acceptance: `MetaState::drain_postponed_levels` re-solves the queue at the
/// declaration boundary and errors on anything left. A definite conflict fails
/// here, immediately, exactly as before.
/// `Some(l')` when `l` is a `Succ` tower in disguise — `l = l' + 1` for every
/// assignment of its parameters: a literal `Succ`, or a `Max`/`IMax` all of
/// whose branches are (`max(a+1, b+1) = (max a b)+1`, and `imax(a+1, b+1) =
/// max(a+1, b+1)` because `b+1` is never zero). `None` for anything else, so
/// the caller keeps its conservative fallthrough.
fn peel_succ(l: &Level) -> Option<Level> {
    match l {
        Level::Succ(inner) => Some(inner.as_ref().clone()),
        Level::Max(a, b) | Level::IMax(a, b) => {
            let a1 = peel_succ(a)?;
            let b1 = peel_succ(b)?;
            Some(Level::max(a1, b1))
        }
        _ => None,
    }
}

pub(crate) fn solve_level_eq(metas: &mut MetaState, l1: &Level, l2: &Level) -> UnifyResult {
    solve_level_eq_impl(metas, l1, l2, true)
}

/// As [`solve_level_eq`] but never defers — used by the drain, which must not
/// re-queue the equation it is trying to discharge.
pub(crate) fn solve_level_eq_no_postpone(
    metas: &mut MetaState,
    l1: &Level,
    l2: &Level,
) -> UnifyResult {
    solve_level_eq_impl(metas, l1, l2, false)
}

fn solve_level_eq_impl(
    metas: &mut MetaState,
    l1: &Level,
    l2: &Level,
    may_postpone: bool,
) -> UnifyResult {
    stack_safe(|| {
        // First, instantiate any already-solved level params.
        let l1 = metas.instantiate_level(l1);
        let l2 = metas.instantiate_level(l2);

        if l1 == l2 {
            return UnifyResult::Success;
        }

        match (&l1, &l2) {
            // Both params: constrain one to the other, but NEVER rename a
            // rigid declared universe parameter onto a fresh elaboration
            // param — assign the fresh one so the user's universe name
            // survives (see the primary-site history: `Inh.{u_0} α` inside
            // `structure S (α : Sort u)` must not rename `u` to `u_0`).
            (Level::Param(name1), Level::Param(name2)) => {
                if metas.is_rigid_level_param(name1) && !metas.is_rigid_level_param(name2) {
                    assign(metas, name2.clone(), l1.clone())
                } else {
                    assign(metas, name1.clone(), l2.clone())
                }
            }
            // Param vs concrete (either side).
            (Level::Param(name), _) if !l2.has_params() => assign(metas, name.clone(), l2.clone()),
            (_, Level::Param(name)) if !l1.has_params() => assign(metas, name.clone(), l1.clone()),

            // Succ decomposition (recursion cancels whole towers).
            (Level::Succ(inner1), Level::Succ(inner2)) => {
                solve_level_eq_impl(metas, inner1, inner2, may_postpone)
            }

            // `0 =?= succ l` has NO solution — `succ l ≥ 1` whatever `l` is —
            // so it is refuted outright, never postponed. Lean's `solve`
            // (`Lean/Meta/LevelDefEq.lean`): `| Level.zero, Level.succ .. =>
            // return LBool.false`, tried in both orientations. It used to fall
            // to the tail below, where a `?u` in `succ ?u` made the equation
            // "undetermined" and it was POSTPONED — accepted for now — so a
            // Prop-only instance candidate survived its level check at a
            // `Type`-sorted carrier: `Mathlib/Logic/Function/Basic.lean`'s
            // `partialInv {α β}` (`Option α` forces `α : Sort (succ ?u)`)
            // committed `exists_prop_decidable` (`Exists.{0}`) for
            // `Decidable (∃ a, f a = b)` and died at the declaration-boundary
            // drain with `unresolved universe level equation after
            // postponement: Zero =?= Succ(?u_4)`. Refuted here, the candidate
            // fails and the search moves to the next one, as in Lean.
            (Level::Zero, Level::Succ(_)) | (Level::Succ(_), Level::Zero) => {
                UnifyResult::Failure(format!("universe level conflict: {l1} vs {l2}"))
            }

            // Param vs Succ(..), occurs-checked (self-referential equations
            // like `u = Succ(u)` are unsatisfiable and would loop during
            // instantiation without the check).
            (Level::Param(name), Level::Succ(_)) => {
                if level_param_occurs(name, &l2) {
                    UnifyResult::Failure(format!(
                        "occurs check failed for level param {name} in {l2}"
                    ))
                } else {
                    assign(metas, name.clone(), l2.clone())
                }
            }
            (Level::Succ(_), Level::Param(name)) => {
                if level_param_occurs(name, &l1) {
                    UnifyResult::Failure(format!(
                        "occurs check failed for level param {name} in {l1}"
                    ))
                } else {
                    assign(metas, name.clone(), l1.clone())
                }
            }

            // Miller-style slice for Max/IMax: an unassigned param head takes
            // the whole expression, occurs-checked. Provisional — the result
            // is kernel-checked, so a wrong commitment fails downstream.
            // RIGID param vs Max/IMax(metas): the param cannot be assigned;
            // solve the OPERANDS to the rigid param instead (max(u,u) = u,
            // imax(u,u) = u — sound, provisional, kernel-rechecked). Measured:
            // the .{u} codata type def over the two-universe seeds constrains
            // `Type (max ?fam ?idx) =?= Type u` before either meta is pinned.
            //
            // That componentwise commitment is GREEDY, and wrong whenever one
            // operand is later pinned to something else: instance search
            // pre-checks `Compl.{max ?ι ?π} =?= Compl.{u}` for `Compl (α → Prop)`
            // through `Pi.instCompl`, where `?ι := u` and `?π := 0` (`Prop :
            // Type 0`) are the real solution and `max u 0 = u`. Committing
            // `?π := u` here made the `Prop.instCompl` subgoal fail
            // (`Mathlib/Order/Basic.lean`: `compl_lt`, `compl_le`, `compl_gt`,
            // `compl_ge`, `Std.Refl.compl`, `Std.Irrefl.compl`,
            // `Ne.instIsEquiv_compl`, measured 2026-09-11). So while an operand
            // is still an unassigned metavariable the equation is POSTPONED
            // (Lean does the same: `max ?u ?v =?= w` is stuck, not solved), and
            // the greedy rule runs only at the no-postpone drain, when nothing
            // else could pin the operands.
            (Level::Param(name), Level::Max(a, b) | Level::IMax(a, b)) => {
                if metas.is_rigid_level_param(name) {
                    if may_postpone && metas.level_eq_is_undetermined(&l1, &l2) {
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        return UnifyResult::Success;
                    }
                    match solve_level_eq_impl(metas, a, &l1, may_postpone) {
                        UnifyResult::Success => solve_level_eq_impl(metas, b, &l1, may_postpone),
                        other => other,
                    }
                } else if level_param_occurs(name, &l2) {
                    // `?x =?= max ?x ?y` is SATISFIABLE (`?y ≤ ?x`), not
                    // circular: the search for `Compl (α → Prop)` through
                    // `Pi.instCompl` poses it with `?y` still to be pinned by
                    // the `Prop.instCompl` subgoal (`?y := 0`, then
                    // `max ?x 0 = ?x`). Refusing it here killed that candidate
                    // (measured 2026-09-11 with `CLEAN_INSTANCE_TRACE`); it is
                    // postponed while postponement is allowed and only the
                    // drain, with every other equation solved, refuses it.
                    if may_postpone {
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        return UnifyResult::Success;
                    }
                    UnifyResult::Failure(format!(
                        "occurs check failed for level param {name} in {l2}"
                    ))
                } else {
                    assign(metas, name.clone(), l2.clone())
                }
            }
            (Level::Max(a, b) | Level::IMax(a, b), Level::Param(name)) => {
                if metas.is_rigid_level_param(name) {
                    if may_postpone && metas.level_eq_is_undetermined(&l1, &l2) {
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        return UnifyResult::Success;
                    }
                    match solve_level_eq_impl(metas, a, &l2, may_postpone) {
                        UnifyResult::Success => solve_level_eq_impl(metas, b, &l2, may_postpone),
                        other => other,
                    }
                } else if level_param_occurs(name, &l1) {
                    if may_postpone {
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        return UnifyResult::Success;
                    }
                    UnifyResult::Failure(format!(
                        "occurs check failed for level param {name} in {l1}"
                    ))
                } else {
                    assign(metas, name.clone(), l1.clone())
                }
            }

            // Rung-3 Succ-distribution over Max: max(a+1, b+1) is
            // definitionally (max a b)+1, so `max(Succ a, Succ b) =?= Succ c`
            // reduces to `max(a, b) =?= c` (both directions). Lean's
            // Level.normalize performs the same lift; Clean's conservative
            // fallthrough previously missed it (measured on the .{u} seed
            // lift: `Max(Succ .., Succ ..) vs Succ(?u)`).
            //
            // The lift is recursive: `max(max(a+1, b+1), c+1)` — the sort of
            // `α₁ ⊕ α₂ → β` over three `Type*` variables, which `Pi.hasLe`
            // meets in `Mathlib/Order/Basic.lean`'s `Sum.elim_le_elim_iff` —
            // is `(max (max a b) c)+1` too, and `imax(a+1, b+1)` is
            // `max(a+1, b+1)` since its right side is never zero. Measured
            // 2026-09-11: the one-level form stopped at the nested `max`
            // with `level mismatch: ?u+1 vs max(max(?a+1, ?b+1), ?c+1)`.
            (Level::Max(a, b), Level::Succ(c)) | (Level::Succ(c), Level::Max(a, b)) => {
                if let Some(inner) = peel_succ(&Level::max(a.as_ref().clone(), b.as_ref().clone()))
                {
                    solve_level_eq_impl(metas, &inner, c, may_postpone)
                } else if Level::is_def_eq(&l1, &l2) {
                    UnifyResult::Success
                } else {
                    crate::u2_histogram::u2_hist(
                        "algebraic-maximax",
                        "solver-succ-max-arm",
                        &format!(
                            "{} =?= {}",
                            crate::u2_histogram::level_str(&l1),
                            crate::u2_histogram::level_str(&l2)
                        ),
                    );
                    UnifyResult::Failure(format!("level mismatch: {l1} vs {l2}"))
                }
            }

            // Rung-3 most-general decompositions against Zero. These are the
            // only Max/IMax equations with a unique most-general solution:
            //   max(a,b) = 0  ⟺  a = 0 ∧ b = 0
            //   imax(a,b) = 0 ⟺  b = 0        (imax _ 0 = 0; b > 0 forces
            //                                   imax = max ≥ b > 0)
            // Congruence decomposition: max/imax against the SAME head.
            //
            // `a = c ∧ b = d` is SUFFICIENT for `max(a,b) = max(c,d)` but not
            // NECESSARY — `max(0,u) =?= max(u,0)` holds while the componentwise
            // split fails. So unlike the Zero-RHS arms below (where both
            // components being zero is the most-general solution, and a failure
            // there is a real failure), this attempt must leave NO trace when
            // it does not work: it runs in its own scope, commits on success,
            // and rolls back and falls through to normalization / `is_def_eq` /
            // postponement otherwise. Without the rollback a half-applied split
            // would wrongly constrain every later equation.
            (Level::Max(a, b), Level::Max(c, d)) | (Level::IMax(a, b), Level::IMax(c, d)) => {
                // `max` is COMMUTATIVE and this split is POSITIONAL, so when
                // the SWAPPED pairing solves the equation too, committing the
                // positional one is a CHOICE — and a wrong one half the time.
                // `imax` is not commutative and is excluded.
                //
                // Measured 2026-09-21. Lean's serializer normalises a `max`
                // into an order that need not be the one Clean's elaborator
                // built the goal in: on the pinned v4.30.0-rc2,
                // `#check @instInhabitedProd` prints
                // `Inhabited.{max (u_2 + 1) (u_1 + 1)} (Prod.{u_1, u_2} α β)`
                // — `u_2` first in the class level, `u_1` first in `Prod` —
                // while Clean reads the goal's level off `Prod`'s own result
                // sort (`env/core.rs`: `Sort (max (u+1) (v+1))`), in source
                // order. The positional split then solved
                // `max (?b+1) (?a+1) =?= max (u+1) (v+1)` as `?b := u`,
                // `?a := v`, the CROSSED solution; the argument unification
                // that follows posed `Prod.{?a, ?b} ?m0 ?m1 =?= Prod.{u, v}
                // A A'` and died `cannot assign rigid universe parameter
                // v := u` (`Mathlib/Logic/Function/Basic.lean`:
                // `Function.curry_update`, `Function.uncurry_update_update`,
                // which need `DecidableEq (α × α')` at `{α α' : Type*}`).
                // Both pairings satisfy the class-level equation, so nothing
                // at THIS equation can tell them apart — only the arguments
                // can, which is exactly the situation the neighbouring
                // `Param`-vs-`Max` arms already postpone.
                //
                // Narrow on purpose. The ambiguity test runs only when the
                // two sides are not ALREADY equal (so nothing would have been
                // assigned), only when postponement is allowed, only when an
                // assignable parameter is present, and only when the swapped
                // pairing really does succeed — from the same state, in its
                // own rolled-back scope. A candidate whose operands pair only
                // one way (`HasEquiv.{u,v}`, whose class level no argument
                // fixes) still takes the split and still commits it.
                let commutative = matches!((&l1, &l2), (Level::Max(..), Level::Max(..)));
                let pairing_is_ambiguous = commutative
                    && may_postpone
                    && !Level::is_def_eq(&l1, &l2)
                    && metas.level_eq_is_undetermined(&l1, &l2)
                    && {
                        metas.push_scope();
                        let swapped = matches!(
                            match solve_level_eq_impl(metas, a, d, false) {
                                UnifyResult::Success => solve_level_eq_impl(metas, b, c, false),
                                other => other,
                            },
                            UnifyResult::Success
                        );
                        metas.pop_scope();
                        swapped
                    };
                if pairing_is_ambiguous {
                    crate::u2_histogram::u2_hist(
                        "level-congruence-split",
                        "solver",
                        "max pairing ambiguous — postponed",
                    );
                    // NOT an acceptance: `drain_postponed_levels` re-solves it
                    // at the declaration boundary, where the arguments have
                    // pinned the operands, and refuses what is still open.
                    metas.postpone_level_eq(l1.clone(), l2.clone());
                    return UnifyResult::Success;
                }
                metas.push_scope();
                let split = match solve_level_eq_impl(metas, a, c, false) {
                    UnifyResult::Success => solve_level_eq_impl(metas, b, d, false),
                    other => other,
                };
                if matches!(split, UnifyResult::Success) {
                    metas.commit();
                    crate::u2_histogram::u2_hist(
                        "level-congruence-split",
                        "solver",
                        "max/imax componentwise",
                    );
                    UnifyResult::Success
                } else {
                    metas.pop_scope();
                    // Fall through to the conservative tail: normalization can
                    // still equate reordered/absorbed forms the split misses.
                    if Level::is_def_eq(&l1, &l2) {
                        UnifyResult::Success
                    } else if may_postpone && metas.level_eq_is_undetermined(&l1, &l2) {
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        UnifyResult::Success
                    } else {
                        UnifyResult::Failure(format!("level mismatch: {l1} vs {l2}"))
                    }
                }
            }

            (Level::Max(a, b), Level::Zero) | (Level::Zero, Level::Max(a, b)) => {
                match solve_level_eq_impl(metas, a, &Level::Zero, may_postpone) {
                    UnifyResult::Success => {
                        solve_level_eq_impl(metas, b, &Level::Zero, may_postpone)
                    }
                    other => other,
                }
            }
            (Level::IMax(_, b), Level::Zero) | (Level::Zero, Level::IMax(_, b)) => {
                solve_level_eq_impl(metas, b, &Level::Zero, may_postpone)
            }

            // Max/IMax of two ASSIGNABLE params vs a CONCRETE level: assign
            // both operands the target (max(c,c) = imax(c,c) = c — sound,
            // provisional, kernel-rechecked). Measured wall: `congrFun h a`
            // over Nat → Nat dies on `imax(?u,?v) =?= 1` because the imax
            // constraint arrives before α/β pin the metas; Lean solves the
            // same shape. Rigid operands fall through (no unique solution).
            (Level::Max(a, b) | Level::IMax(a, b), _)
                if !l2.has_params()
                    && matches!((a.as_ref(), b.as_ref()),
                        (Level::Param(x), Level::Param(y))
                        if !metas.is_rigid_level_param(x)
                            && !metas.is_rigid_level_param(y)) =>
            {
                match solve_level_eq_impl(metas, a, &l2, may_postpone) {
                    UnifyResult::Success => solve_level_eq_impl(metas, b, &l2, may_postpone),
                    other => other,
                }
            }
            (_, Level::Max(a, b) | Level::IMax(a, b))
                if !l1.has_params()
                    && matches!((a.as_ref(), b.as_ref()),
                        (Level::Param(x), Level::Param(y))
                        if !metas.is_rigid_level_param(x)
                            && !metas.is_rigid_level_param(y)) =>
            {
                match solve_level_eq_impl(metas, a, &l1, may_postpone) {
                    UnifyResult::Success => solve_level_eq_impl(metas, b, &l1, may_postpone),
                    other => other,
                }
            }

            // Conservative fallthrough: normalize + is_def_eq, else Failure.
            _ => {
                if Level::is_def_eq(&l1, &l2) {
                    crate::u2_histogram::u2_hist(
                        "algebraic-defeq-saved",
                        "solver",
                        "normalization-only success",
                    );
                    UnifyResult::Success
                } else {
                    if crate::u2_histogram::u2_hist_enabled() {
                        let l1_rigid = matches!(&l1, Level::Param(n)
                            if metas.is_rigid_level_param(n));
                        let l2_rigid = matches!(&l2, Level::Param(n)
                            if metas.is_rigid_level_param(n));
                        let class = crate::u2_histogram::classify_level_failure(
                            &l1, &l2, l1_rigid, l2_rigid,
                        );
                        crate::u2_histogram::u2_hist(
                            class,
                            "solver",
                            &format!(
                                "{} =?= {}",
                                crate::u2_histogram::level_str(&l1),
                                crate::u2_histogram::level_str(&l2)
                            ),
                        );
                    }
                    if !l1.has_params() && !l2.has_params() {
                        // DEFINITE conflict: both sides ground and unequal.
                        // Never deferred — no later assignment can change it.
                        UnifyResult::Failure(format!("universe level conflict: {l1} vs {l2}"))
                    } else if may_postpone && metas.level_eq_is_undetermined(&l1, &l2) {
                        // UNDETERMINED: some side still mentions a solvable
                        // parameter, so a later assignment may settle this.
                        // Deferred, NOT accepted — `drain_postponed_levels`
                        // re-solves at the declaration boundary and errors on
                        // whatever is left.
                        crate::u2_histogram::u2_hist(
                            "level-postponed",
                            "solver",
                            "deferred undetermined equation",
                        );
                        metas.postpone_level_eq(l1.clone(), l2.clone());
                        UnifyResult::Success
                    } else {
                        UnifyResult::Failure(format!("level mismatch: {l1} vs {l2}"))
                    }
                }
            }
        }
    })
}
