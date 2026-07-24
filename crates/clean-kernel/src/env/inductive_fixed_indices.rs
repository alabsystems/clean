// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fixed-index computation and promotion for inductive types.
//!
//! Implements Lean 4's `fixedIndicesToParams` from
//! `src/Lean/Elab/MutualInductive.lean`, determining which index
//! positions are "fixed" across all constructors and can be promoted
//! to parameters.

use crate::expr::{Expr, ExprKind};
use crate::inductive::{count_pi_args, get_return_type, strip_pi, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

/// Check if an expression's head is a `Const` matching one of the given names.
pub(crate) fn expr_head_is_ind(e: &Expr, ind_names: &[Name]) -> bool {
    let mut head = e;
    while let ExprKind::App(f, _) = &head.kind {
        head = f;
    }
    matches!(&head.kind, ExprKind::Const(n, _) if ind_names.contains(n))
}

/// Walk an expression, calling `f(occurrence, extra_depth)` on each
/// subexpression whose head (after stripping App) is a `Const` matching one
/// of `ind_names`. `extra_depth` counts the number of binders (Pi/Lam/Let)
/// entered since the walk began, which is needed to adjust BVar comparisons.
pub(crate) fn for_each_ind_occurrence_depth(
    e: &Expr,
    ind_names: &[Name],
    depth: u32,
    f: &mut impl FnMut(&Expr, u32),
) {
    match &e.kind {
        ExprKind::App(_, _) => {
            if expr_head_is_ind(e, ind_names) {
                f(e, depth);
            }
            // Also recurse into sub-expressions (the function and argument)
            let mut cur = e;
            while let ExprKind::App(func, arg) = &cur.kind {
                for_each_ind_occurrence_depth(arg, ind_names, depth, f);
                cur = func;
            }
        }
        ExprKind::Pi(_, domain, body) | ExprKind::Lam(_, domain, body) => {
            for_each_ind_occurrence_depth(domain, ind_names, depth, f);
            for_each_ind_occurrence_depth(body, ind_names, depth + 1, f);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            for_each_ind_occurrence_depth(ty, ind_names, depth, f);
            for_each_ind_occurrence_depth(val, ind_names, depth, f);
            for_each_ind_occurrence_depth(body, ind_names, depth + 1, f);
        }
        _ => {}
    }
}

/// Compute a bitmask of which index positions are "fixed" for a single inductive type.
///
/// An index position `i` (0-indexed from the first index) is "fixed" if:
/// 1. Every constructor has a constructor argument at position `num_params + i`
///    that appears directly as the corresponding argument in the constructor's
///    return type (direct check).
/// 2. Every recursive occurrence of an inductive type in constructor field types
///    also uses the same argument at that index position (recursive check).
///
/// This mirrors Lean 4's `computeFixedIndexBitMask` from
/// `src/Lean/Elab/MutualInductive.lean`, operating purely syntactically
/// on de Bruijn indices (no MetaM / definitional equality).
///
/// Returns a `Vec<bool>` of length `num_indices` where `true` means the
/// index at that position is fixed across all constructors.
pub(crate) fn compute_fixed_index_mask(
    ind_type: &InductiveType,
    num_params: u32,
    ind_names: &[Name],
) -> Vec<bool> {
    let type_arity = count_pi_args(&ind_type.type_);
    let num_indices = type_arity.saturating_sub(num_params) as usize;
    if num_indices == 0 {
        return vec![];
    }

    // Start optimistic: every index is potentially fixed
    let mut mask = vec![true; num_indices];

    for ctor in &ind_type.constructors {
        let ctor_arity = count_pi_args(&ctor.type_);
        let ctor_return = get_return_type(&ctor.type_);
        let ret_args = ctor_return.get_app_args();

        // Phase 1: Direct check — constructor argument at position num_params+i
        // must appear as BVar at the same position in the return type.
        #[allow(clippy::needless_range_loop)]
        // idx_pos used for arg_pos computation, not just mask indexing
        for idx_pos in 0..num_indices {
            if !mask[idx_pos] {
                continue;
            }

            let arg_pos = num_params as usize + idx_pos;

            if arg_pos >= ctor_arity as usize || arg_pos >= ret_args.len() {
                mask[idx_pos] = false;
                continue;
            }

            // Under ctor_arity binders, argument at position arg_pos is
            // BVar(ctor_arity - 1 - arg_pos).
            let expected_bvar = ctor_arity as usize - 1 - arg_pos;
            let is_fixed = matches!(
                &ret_args[arg_pos].kind,
                ExprKind::BVar(v) if *v == expected_bvar as u32
            );
            if !is_fixed {
                mask[idx_pos] = false;
            }
        }

        // Phase 2: Recursive occurrence check — for each constructor field
        // after parameters, walk its type. Any application of an inductive
        // type in the mutual block must use the SAME constructor argument at
        // each index position. If a recursive occurrence uses a different
        // variable, that index position is not truly fixed.
        //
        // This catches cases like Acc.intro where the return type has
        // `Acc r x` (x fixed) but a field type contains `Acc r y` (y ≠ x).
        //
        // BVar scoping: the domain of binder at position `binder_idx` is
        // under `binder_idx` binders. Within that domain, `extra_depth`
        // additional binders may exist. Constructor arg at position `p`
        // (where p < binder_idx) is BVar(binder_idx + extra_depth - 1 - p)
        // in that context, vs BVar(ctor_arity - 1 - p) in ret_args.
        //
        // Lean 4 ref: computeFixedIndexBitMask, `for x in xs[numParams...]`.
        let mut cur_ty = &ctor.type_;
        for binder_idx in 0..ctor_arity {
            if let ExprKind::Pi(_, domain, body) = &cur_ty.kind {
                if binder_idx >= num_params {
                    let bi = binder_idx;
                    for_each_ind_occurrence_depth(domain, ind_names, 0, &mut |occ, extra_depth| {
                        let occ_args = occ.get_app_args();
                        let total_depth = bi + extra_depth;
                        #[allow(clippy::needless_range_loop)]
                        for idx_pos in 0..num_indices {
                            if !mask[idx_pos] {
                                continue;
                            }
                            let arg_pos = num_params as usize + idx_pos;
                            if arg_pos >= occ_args.len() {
                                mask[idx_pos] = false;
                                continue;
                            }
                            // In ret_args scope (ctor_arity binders):
                            // arg at arg_pos is BVar(ctor_arity - 1 - arg_pos)
                            // In occurrence scope (total_depth binders from
                            // ctor's Pi-chain + extra from field type):
                            // arg at arg_pos is BVar(total_depth - 1 - arg_pos)
                            // if arg_pos < total_depth (referencing an outer binder)
                            if (arg_pos as u32) >= total_depth {
                                // This arg position is not reachable from
                                // the current scope — mark as not fixed
                                mask[idx_pos] = false;
                                continue;
                            }
                            let expected_bvar_in_occ = total_depth as usize - 1 - arg_pos;
                            let is_match = matches!(
                                &occ_args[arg_pos].kind,
                                ExprKind::BVar(v) if *v == expected_bvar_in_occ as u32
                            );
                            if !is_match {
                                mask[idx_pos] = false;
                            }
                        }
                    });
                }
                cur_ty = body;
            } else {
                break;
            }
        }
    }

    mask
}

/// Compute the number of index positions that can be promoted to parameters.
///
/// Implements the equivalent of Lean 4's `fixedIndicesToParams` from
/// `src/Lean/Elab/MutualInductive.lean`. Only promotes a contiguous prefix
/// of indices that are fixed across ALL inductive types in the mutual block,
/// and whose domains are syntactically identical across all types and
/// constructor types at that position.
///
/// Returns the new `num_params` (>= the original).
pub(crate) fn fixed_indices_to_params(decl: &InductiveDecl) -> u32 {
    let num_params = decl.num_params;

    // Collect all inductive type names for recursive occurrence detection
    let ind_names: Vec<Name> = decl.types.iter().map(|t| t.name.clone()).collect();

    // Compute fixed-index masks for all inductive types
    let masks: Vec<Vec<bool>> = decl
        .types
        .iter()
        .map(|ind_type| compute_fixed_index_mask(ind_type, num_params, &ind_names))
        .collect();

    // If no type has any indices, nothing to promote
    if masks.iter().all(|m| m.is_empty()) {
        return num_params;
    }

    // Find the contiguous prefix of indices that are fixed in ALL types.
    // Also verify that the domain types at each promoted position are
    // syntactically identical across the first inductive type and all
    // constructor types (simplified check: we verify the domain of the
    // first type's Pi binder at that position).
    let first_type = &decl.types[0];
    let first_mask = &masks[0];

    let mut promoted = 0u32;
    for idx_pos in 0..first_mask.len() {
        // Check that ALL masks have this position as fixed
        let all_fixed = masks.iter().all(|m| idx_pos < m.len() && m[idx_pos]);
        if !all_fixed {
            break; // Stop at first non-fixed position (contiguous prefix only)
        }

        // Verify the domain type at this position in the inductive type
        // is a well-formed Pi binder. We strip num_params + idx_pos Pi's
        // from the type and check we still have a Pi.
        let remaining = strip_pi(&first_type.type_, num_params + idx_pos as u32);
        if !matches!(&remaining.kind, ExprKind::Pi(_, _, _)) {
            break; // Not a Pi binder at this position — can't promote
        }

        // For mutual inductives, verify all other types also have a Pi
        // at this position (their domains should be compatible)
        let all_have_pi = decl.types.iter().all(|t| {
            let r = strip_pi(&t.type_, num_params + idx_pos as u32);
            matches!(&r.kind, ExprKind::Pi(_, _, _))
        });
        if !all_have_pi {
            break;
        }

        promoted += 1;
    }

    num_params + promoted
}

/// Packed constructor field info for recursor generation:
/// - `name`: Constructor name
/// - `num_fields`: Number of fields (after parameters)
/// - `recursive_flags`: Which fields are recursive occurrences of the inductive type
/// - `field_types`: Field type expressions
/// - `return_indices`: Index expressions from constructor's return type
pub(crate) type CtorInfo = (Name, u32, Vec<bool>, Vec<Expr>, Vec<Expr>);

/// Build a `Const` expression for an inductive type with proper universe level params.
pub(crate) fn ind_const_with_levels(name: &Name, level_params: &[Name]) -> Expr {
    let levels: Vec<Level> = level_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect();
    Expr::const_(name.clone(), levels)
}

/// Pick a fresh universe parameter name that does not collide with `existing`.
/// Starts with `"u"` and appends numeric suffixes (`"u_1"`, `"u_2"`, ...) until unique.
pub(crate) fn fresh_univ_name(existing: &[Name]) -> Name {
    let candidate = Name::from_string("u");
    if !existing.contains(&candidate) {
        return candidate;
    }
    for i in 1u32.. {
        let candidate = Name::from_string(&format!("u_{i}"));
        if !existing.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!("infinite loop should find a fresh name")
}

/// Check if a type is a "prop former" — its type, after stripping all Pi
/// binders, ends in `Sort(Zero)` (i.e., `Prop`).
///
/// Lean 4 skips noConfusion generation for prop-valued inductive types
/// (see `Lean/Meta/Constructions/NoConfusion.lean:359`).
pub(crate) fn is_prop_former_type(type_: &Expr) -> bool {
    let mut cur = type_;
    loop {
        match &cur.kind {
            ExprKind::Pi(_, _, body) => cur = body,
            ExprKind::Sort(level) => return level.is_zero(),
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinderInfo;
    use crate::inductive::Constructor;
    use crate::level::Level;

    /// Eq-like: single constructor with a fixed index → promotes 1 index.
    ///
    /// Eq : {α : Sort u} → α → α → Prop (num_params=1, 2 indices)
    /// Eq.refl : {α : Sort u} → (a : α) → Eq α a a (ctor_arity=2)
    ///
    /// Index 0 (first `a` in `Eq α a a`): BVar(0) in ret, matches ctor arg 1.
    /// Index 1 (second `a`): ctor_arity=2 so arg_pos=2 >= ctor_arity → not fixed.
    /// Result: mask=[true, false], promotes 1. New num_params=2.
    #[test]
    fn test_fixed_indices_eq_promotes_one() {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

        // Eq : {α : Sort u} → α → α → Prop
        let eq_type = {
            // Pi{α : Sort u}. Pi(a : α). Pi(b : α). Prop
            let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(0),                                      // α
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), prop), // α, Prop
                ),
            )
        };

        // Eq.refl : {α : Sort u} → (a : α) → Eq α a a
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]);
        let refl_type = {
            // Pi{α : Sort u}. Pi(a : α). Eq α a a
            // Under 2 binders: α=BVar(1), a=BVar(0)
            let eq_a_a = Expr::app(
                Expr::app(Expr::app(eq_const, Expr::bvar(1)), Expr::bvar(0)),
                Expr::bvar(0),
            );
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), eq_a_a),
            )
        };

        let decl = InductiveDecl {
            level_params: vec![u],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Eq"),
                type_: eq_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Eq.refl"),
                    type_: refl_type,
                }],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(new_num_params, 2, "Eq should promote 1 index to parameter");
    }

    /// Acc-like: fixed return-type index but different in recursive field → no promotion.
    ///
    /// Acc : {α : Sort u} → (r : α → α → Prop) → α → Prop
    /// Acc.intro : {α} → (r) → (x : α) → (h : ∀ y, r y x → Acc r y) → Acc r x
    ///
    /// Return type: Acc α r x → index 0 has BVar(1)=x. Matches direct check.
    /// But field h's type contains `Acc α r y` where y is a different BVar.
    /// Recursive occurrence check catches this → mask[0]=false.
    #[test]
    fn test_fixed_indices_acc_no_promotion() {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let acc_name = Name::from_string("Acc");
        let acc_const = Expr::const_(acc_name.clone(), vec![Level::param(u.clone())]);

        // Acc : {α : Sort u} → (r : α → α → Prop) → α → Prop
        // Under 3 binders: α=BVar(2), r=BVar(1), x=BVar(0)
        let acc_type = {
            // r type: α → α → Prop
            let r_type = Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),                                              // α
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // α → Prop
            );
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    r_type,
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // α → Prop
                ),
            )
        };

        // Acc.intro : {α} → (r : α→α→Prop) → (x : α) → (h : ∀ y, r y x → Acc r y) → Acc r x
        // Under 4 binders: α=BVar(3), r=BVar(2), x=BVar(1), h=BVar(0)
        let acc_intro_type = {
            let r_type = Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0), // α
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()),
            );
            // h_type: ∀ y, r y x → Acc α r y
            // h_type is the domain of the 4th Pi in the ctor type, viewed
            // under 3 prior binders (α, r, x).
            // Top-level: α=BVar(2), r=BVar(1), x=BVar(0)
            // After ∀ y: α=BVar(3), r=BVar(2), x=BVar(1), y=BVar(0)
            // After r y x →: α=BVar(4), r=BVar(3), x=BVar(2), y=BVar(1)
            let h_type = {
                // r y x: viewed under {α,r,x,y} = 4 binders from h_type scope
                let r_y_x = Expr::app(
                    Expr::app(Expr::bvar(2), Expr::bvar(0)), // r y
                    Expr::bvar(1),                           // x
                );
                // Acc α r y: viewed under {α,r,x,y,anon} = 5 binders from h_type
                let acc_r_y = Expr::app(
                    Expr::app(
                        Expr::app(acc_const.clone(), Expr::bvar(4)), // α
                        Expr::bvar(3),                               // r
                    ),
                    Expr::bvar(1), // y
                );
                // ∀ (y : α), r y x → Acc α r y
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(2), // α (viewed under {α,r,x} = 3 binders)
                    Expr::pi(BinderInfo::Default, r_y_x, acc_r_y),
                )
            };

            // Return type: Acc α r x
            // Under 4 binders: α=BVar(3), r=BVar(2), x=BVar(1)
            let acc_r_x = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), Expr::bvar(3)), Expr::bvar(2)),
                Expr::bvar(1),
            );

            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    r_type,
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1), // α
                        Expr::pi(BinderInfo::Default, h_type, acc_r_x),
                    ),
                ),
            )
        };

        let decl = InductiveDecl {
            level_params: vec![u],
            num_params: 2,
            types: vec![InductiveType {
                name: acc_name,
                type_: acc_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Acc.intro"),
                    type_: acc_intro_type,
                }],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(
            new_num_params, 2,
            "Acc must NOT promote — recursive occurrence uses different variable"
        );
    }

    /// Nat.le-like: two constructors with different index values → no promotion.
    ///
    /// Nat.le : Nat → Nat → Prop (num_params=1, 1 index)
    /// Nat.le.refl : (n : Nat) → Nat.le n n  — index = n (BVar for n)
    /// Nat.le.step : (n m : Nat) → Nat.le n m → Nat.le n (succ m)  — index = succ m
    ///
    /// Direct check: refl has BVar match, step has App(succ, m) → not a BVar.
    /// mask[0] = false. No promotion.
    #[test]
    fn test_fixed_indices_nat_le_no_promotion() {
        let nat = Name::from_string("Nat");
        let nat_ref = Expr::const_(nat.clone(), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let le_name = Name::from_string("Nat.le");
        let le_const = Expr::const_(le_name.clone(), vec![]);

        // Nat.le : Nat → Nat → Prop
        let le_type = Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::pi(BinderInfo::Default, nat_ref.clone(), prop),
        );

        // Nat.le.refl : (n : Nat) → Nat.le n n
        // Under 1 binder: n=BVar(0)
        let refl_type = Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(Expr::app(le_const.clone(), Expr::bvar(0)), Expr::bvar(0)),
        );

        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

        // Nat.le.step : (n : Nat) → (m : Nat) → Nat.le n m → Nat.le n (succ m)
        // Under 3 binders: n=BVar(2), m=BVar(1), h=BVar(0)
        let step_type = Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::app(le_const.clone(), Expr::bvar(1)), // n
                        Expr::bvar(0),                              // m
                    ),
                    Expr::app(
                        Expr::app(le_const, Expr::bvar(2)), // n
                        Expr::app(succ, Expr::bvar(1)),     // succ m
                    ),
                ),
            ),
        );

        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: le_name,
                type_: le_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Nat.le.refl"),
                        type_: refl_type,
                    },
                    Constructor {
                        name: Name::from_string("Nat.le.step"),
                        type_: step_type,
                    },
                ],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(
            new_num_params, 1,
            "Nat.le must NOT promote — step uses succ m, not a direct BVar"
        );
    }

    /// Parametric type with no indices: no promotion, num_params unchanged.
    #[test]
    fn test_fixed_indices_no_indices() {
        let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat : Type, num_params=0, num_indices=0
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Nat"),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Nat.zero"),
                        type_: nat_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Nat.succ"),
                        type_: Expr::arrow(nat_ref.clone(), nat_ref),
                    },
                ],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(new_num_params, 0, "Nat has no indices, nothing to promote");
    }

    /// Vector-like indexed family: varying index across constructors → no promotion.
    ///
    /// Vector : {α : Type u} → Nat → Type u  (num_params=1, 1 index)
    /// Vector.nil  : {α : Type u} → Vector α 0
    /// Vector.cons : {α : Type u} → {n : Nat} → α → Vector α n → Vector α (succ n)
    ///
    /// Type u = Sort (succ u), matching real Lean's Vector: the result level is
    /// provably nonzero, so the [R1] elim gate keeps large elimination.
    ///
    /// Index 0 (n): nil fills with `Nat.zero` (not a BVar), cons fills with
    /// `App(succ, n)` (not a direct BVar). Neither is fixed → no promotion.
    /// Matches Lean 4: Vector has num_params=1, num_indices=1.
    #[test]
    fn test_fixed_indices_vector_no_promotion() {
        let u = Name::from_string("u");
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
        let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
        let vec_name = Name::from_string("Vector");
        let vec_const = Expr::const_(vec_name.clone(), vec![Level::param(u.clone())]);

        // Vector : {α : Type u} → Nat → Type u
        let vec_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, nat_ref.clone(), type_u.clone()),
        );

        // Vector.nil : {α : Type u} → Vector α 0
        // Under 1 binder: α=BVar(0)
        let nil_type = {
            let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let ret = Expr::app(Expr::app(vec_const.clone(), Expr::bvar(0)), zero);
            Expr::pi(BinderInfo::Implicit, type_u.clone(), ret)
        };

        // Vector.cons : {α : Type u} → {n : Nat} → α → Vector α n → Vector α (succ n)
        // Under 4 binders: α=BVar(3), n=BVar(2), x=BVar(1), tail=BVar(0)
        let cons_type = {
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            // tail domain: Vector α n (under 3 binders: α=BVar(2), n=BVar(1))
            let vec_a_n = Expr::app(Expr::app(vec_const.clone(), Expr::bvar(2)), Expr::bvar(1));
            // return: Vector α (succ n) (under 4 binders: α=BVar(3), n=BVar(2))
            let ret = Expr::app(
                Expr::app(vec_const.clone(), Expr::bvar(3)),
                Expr::app(succ, Expr::bvar(2)),
            );
            Expr::pi(
                BinderInfo::Implicit,
                type_u.clone(),
                Expr::pi(
                    BinderInfo::Implicit,
                    nat_ref.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1), // α
                        Expr::pi(BinderInfo::Default, vec_a_n, ret),
                    ),
                ),
            )
        };

        let decl = InductiveDecl {
            level_params: vec![u],
            num_params: 1,
            types: vec![InductiveType {
                name: vec_name,
                type_: vec_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Vector.nil"),
                        type_: nil_type,
                    },
                    Constructor {
                        name: Name::from_string("Vector.cons"),
                        type_: cons_type,
                    },
                ],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(
            new_num_params, 1,
            "Vector must NOT promote — index varies across constructors (0 vs succ n)"
        );
    }

    /// Fin-like type declared with 0 params, 1 index: promotes the fixed index.
    ///
    /// Fin : Nat → Type  (num_params=0, 1 index)
    /// Fin.mk : (n : Nat) → (val : Nat) → (h : Prop) → Fin n
    ///
    /// Index 0 (n): ctor arg 0 is `n`, return type's arg 0 is `n` (BVar match).
    /// No recursive Fin occurrences in field types → mask[0]=true.
    /// Result: promotes 1, new num_params=1. Matches Lean 4: Fin has num_params=1.
    #[test]
    fn test_fixed_indices_fin_like_promotes_one() {
        let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let fin_name = Name::from_string("Fin");
        let fin_const = Expr::const_(fin_name.clone(), vec![]);

        // Fin : Nat → Type
        let fin_type = Expr::pi(BinderInfo::Default, nat_ref.clone(), Expr::type_());

        // Fin.mk : (n : Nat) → (val : Nat) → (h : Prop) → Fin n
        // Under 3 binders: n=BVar(2), val=BVar(1), h=BVar(0)
        // Return: Fin n = App(Const(Fin), BVar(2))
        let mk_type = {
            let ret = Expr::app(fin_const, Expr::bvar(2));
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    nat_ref.clone(),
                    Expr::pi(BinderInfo::Default, prop, ret),
                ),
            )
        };

        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: fin_name,
                type_: fin_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Fin.mk"),
                    type_: mk_type,
                }],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(
            new_num_params, 1,
            "Fin-like should promote 1 index — n is fixed across the single constructor"
        );
    }

    /// HEq-like: constructor arity too small to fill index positions → no promotion.
    ///
    /// HEq : {α : Sort u} → α → {β : Sort u} → β → Prop  (num_params=2, 2 indices)
    /// HEq.refl : {α : Sort u} → (a : α) → HEq α a α a    (ctor_arity=2)
    ///
    /// Index 0 (β at arg_pos=2): ctor_arity=2, arg_pos(2) >= ctor_arity(2) → not fixed.
    /// Result: no promotion, num_params stays at 2.
    /// Matches Lean 4: HEq has num_params=2, num_indices=2.
    #[test]
    fn test_fixed_indices_heq_no_promotion() {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let heq_name = Name::from_string("HEq");
        let heq_const = Expr::const_(heq_name.clone(), vec![Level::param(u.clone())]);

        // HEq : {α : Sort u} → α → {β : Sort u} → β → Prop
        // Under 4 binders: α=BVar(3), a=BVar(2), β=BVar(1), b=BVar(0)
        let heq_type = Expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0), // α
                Expr::pi(
                    BinderInfo::Implicit,
                    sort_u.clone(),
                    Expr::pi(BinderInfo::Default, Expr::bvar(0), prop.clone()), // β → Prop
                ),
            ),
        );

        // HEq.refl : {α : Sort u} → (a : α) → HEq α a α a
        // Under 2 binders: α=BVar(1), a=BVar(0)
        // Return: HEq α a α a = App(App(App(App(Const(HEq), BVar(1)), BVar(0)), BVar(1)), BVar(0))
        let refl_type = {
            let ret = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(heq_const, Expr::bvar(1)), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            );
            Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), ret), // α → ret
            )
        };

        let decl = InductiveDecl {
            level_params: vec![u],
            num_params: 2,
            types: vec![InductiveType {
                name: heq_name,
                type_: heq_type,
                constructors: vec![Constructor {
                    name: Name::from_string("HEq.refl"),
                    type_: refl_type,
                }],
            }],
        };

        let new_num_params = fixed_indices_to_params(&decl);
        assert_eq!(
            new_num_params, 2,
            "HEq must NOT promote — constructor arity (2) < index arg positions (2,3)"
        );
    }
}
