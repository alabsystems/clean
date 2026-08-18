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
fn level_param_occurs(name: &Name, level: &Level) -> bool {
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
            (Level::Param(name), Level::Max(a, b) | Level::IMax(a, b)) => {
                if metas.is_rigid_level_param(name) {
                    match solve_level_eq_impl(metas, a, &l1, may_postpone) {
                        UnifyResult::Success => solve_level_eq_impl(metas, b, &l1, may_postpone),
                        other => other,
                    }
                } else if level_param_occurs(name, &l2) {
                    UnifyResult::Failure(format!(
                        "occurs check failed for level param {name} in {l2}"
                    ))
                } else {
                    assign(metas, name.clone(), l2.clone())
                }
            }
            (Level::Max(a, b) | Level::IMax(a, b), Level::Param(name)) => {
                if metas.is_rigid_level_param(name) {
                    match solve_level_eq_impl(metas, a, &l2, may_postpone) {
                        UnifyResult::Success => solve_level_eq_impl(metas, b, &l2, may_postpone),
                        other => other,
                    }
                } else if level_param_occurs(name, &l1) {
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
            (Level::Max(a, b), Level::Succ(c)) | (Level::Succ(c), Level::Max(a, b)) => {
                if let (Level::Succ(a1), Level::Succ(b1)) = (a.as_ref(), b.as_ref()) {
                    let inner = Level::max(a1.as_ref().clone(), b1.as_ref().clone());
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
