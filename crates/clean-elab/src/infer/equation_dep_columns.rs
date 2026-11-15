// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ledger class (88), brick B4 of `designs/2026-10-08-mutual-nested-recursion.md`:
//! an equation-form declaration whose trailing columns are hypotheses typed by
//! the earlier, matched ones.
//!
//! ```text
//! theorem one_dep : ∀ n : Nat, isZ n = true → n = 0
//!   | 0, _ => rfl
//!   | _ + 1, h => absurd h …          -- h : isZ (n + 1) = true
//! ```
//!
//! Lean matches every column at once with a motive over all of them, so in
//! each alternative `h` is about that alternative's constructor. Clean's
//! single-declaration lowering lifted `h` to a declaration binder in front of
//! the case split, where it stayed `isZ n = true` (pinned Lean 4.8.0 accepts
//! `one_dep`, `j10.lean`'s `ok_t2` / `ok_t3`). Here the trailing run of such
//! columns is generalized instead: it becomes part of the case split's result
//! type, `∀ h : isZ n = true, n = 0`, and each alternative binds it with
//! `fun h => …`, so the elaborated match specializes it per constructor —
//! Lean's motive, built from surface syntax.
//!
//! Only columns every alternative binds with a plain variable or `_` are
//! generalized (a leaf that could name a constructor keeps the column where
//! it was), and only from the first one whose type names an earlier MATCHED
//! column onward: a hypothesis about a pass-through column needs nothing.

use clean_parser::SurfaceName;
use clean_parser::{
    SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceMatchArm, SurfacePattern,
};

use super::elab_decl_value::{expr_may_mention_ident, PatternIdents};

/// The declaration once its trailing dependent columns are generalized.
pub(super) struct Generalized {
    /// How many leading columns stay matched or lifted.
    pub(super) keep: usize,
    /// `∀ (generalized columns), return type`.
    pub(super) return_ty: SurfaceExpr,
    /// Each alternative with its generalized columns dropped from its
    /// pattern and bound by a `fun` around its body.
    pub(super) arms: Vec<SurfaceMatchArm>,
}

type Domain = (SurfaceExpr, Option<SurfaceName>, SurfaceBinderInfo);

/// Generalize the trailing dependent hypothesis columns, or `None` when
/// there are none (the declaration is then lowered exactly as before).
pub(super) fn generalize_dependent_columns(
    idents: &PatternIdents<'_>,
    domains: &[Domain],
    return_ty: &SurfaceExpr,
    arm_leaves: &[Vec<SurfacePattern>],
    arms: &[SurfaceMatchArm],
) -> Option<Generalized> {
    let arity = domains.len();
    if arm_leaves.iter().any(|leaves| leaves.len() != arity) || arms.len() != arm_leaves.len() {
        return None;
    }
    let plain = |leaf: &SurfacePattern| match leaf {
        SurfacePattern::Wildcard => true,
        SurfacePattern::Var(name) => {
            !idents.shorthand_suspect(name)
                && matches!(
                    idents.resolve_ctor_idents(leaf, true),
                    SurfacePattern::Var(_)
                )
        }
        _ => false,
    };
    let all_plain = |pos: usize| arm_leaves.iter().all(|leaves| plain(&leaves[pos]));
    // The longest run of plain columns at the end.
    let mut suffix = arity;
    while suffix > 0 && all_plain(suffix - 1) {
        suffix -= 1;
    }
    // Its first column whose type names an earlier matched column.
    let names_matched = |pos: usize| {
        (0..pos).any(|earlier| {
            !all_plain(earlier)
                && domains[earlier]
                    .1
                    .as_ref()
                    .is_some_and(|name| expr_may_mention_ident(&domains[pos].0, name))
        })
    };
    let keep = (suffix..arity).find(|&pos| names_matched(pos))?;
    if keep == 0 {
        return None;
    }

    let mut generalized_ty = return_ty.clone();
    for (domain, declared, info) in domains[keep..].iter().rev() {
        let span = domain.span();
        generalized_ty = match (declared, info) {
            (None, SurfaceBinderInfo::Explicit) => {
                SurfaceExpr::Arrow(span, Box::new(domain.clone()), Box::new(generalized_ty))
            }
            _ => {
                let name = declared
                    .clone()
                    .unwrap_or_else(|| SurfaceName::unspellable("_x_dep", keep as u64));
                SurfaceExpr::Pi(
                    span,
                    vec![SurfaceBinder::new_typed(name, Some(domain.clone()), *info)],
                    Box::new(generalized_ty),
                )
            }
        };
    }

    let new_arms = arms
        .iter()
        .zip(arm_leaves)
        .map(|(arm, leaves)| {
            let binders: Vec<SurfaceBinder> = leaves[keep..]
                .iter()
                .zip(&domains[keep..])
                .map(|(leaf, (_, _, info))| {
                    let name = match leaf {
                        SurfacePattern::Var(name) => name.clone(),
                        _ => SurfaceName::component("_", false),
                    };
                    SurfaceBinder::new_typed(name, None, *info)
                })
                .collect();
            SurfaceMatchArm {
                span: arm.span,
                pattern: tuple_pattern(&leaves[..keep]),
                body: SurfaceExpr::Lambda(arm.span, binders, Box::new(arm.body.clone())),
            }
        })
        .collect();
    Some(Generalized {
        keep,
        return_ty: generalized_ty,
        arms: new_arms,
    })
}

/// The right-nested `Prod.mk` tuple the equation parser builds over several
/// columns; a single column is its own pattern.
fn tuple_pattern(leaves: &[SurfacePattern]) -> SurfacePattern {
    match leaves {
        [] => SurfacePattern::Wildcard,
        [only] => only.clone(),
        [first, rest @ ..] => SurfacePattern::Ctor(
            SurfaceName::generated_path("Prod.mk"),
            vec![first.clone(), tuple_pattern(rest)],
        ),
    }
}
