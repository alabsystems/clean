// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict field-occurrence validation ([R8] of
//! `designs/2026-07-02-parameterized-nested-inductives.md` §5.3).
//!
//! Lean's kernel constrains where a block name may appear inside a
//! constructor: a field may mention the block ONLY along its rightmost Pi
//! spine, and the spine core must be a *valid inductive application*
//! (`is_valid_ind_app`, inductive.cpp:338-357) — head is a block member at
//! exactly the declaration's level params, arity is exactly
//! `num_params + num_indices`, the first `num_params` args are exactly the
//! enclosing parameter bvars, and index args are block-free (lean4#2125).
//!
//! Clean's lenient positivity (`check_positivity`) accepts any *positive*
//! occurrence — including non-uniform (`T Nat` in a `T α` block),
//! under-applied, and container-buried (`F (T α)`) shapes — from which the
//! recursor generator emits ill-typed induction hypotheses. This module is
//! the post-transform hard gate: it runs AFTER nested elimination (so
//! container occurrences have been rewritten to direct block applications)
//! and AFTER fixed-index promotion (so the param/index boundary is final),
//! for EVERY inductive declaration, on both the Generate and Skip lanes.
//!
//! Known deliberate divergence from Lean: no `whnf` between steps — a block
//! occurrence hidden behind a definition/redex is rejected rather than
//! unfolded (fail-closed; design §7).

use super::{count_pi_args, get_return_type, mentions_name, InductiveDecl, InductiveError};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Strict post-transform validation of every constructor's field and return
/// occurrences (design §5.3 / [R8]).
///
/// # Errors
///
/// - [`InductiveError::InvalidParams`] — a member's type former has fewer
///   Pi binders than `num_params`.
/// - [`InductiveError::NonPositive`] — a block name occurs in a field's Pi
///   domain (left of an arrow).
/// - [`InductiveError::ConstructorParamMismatch`] — a block application's
///   parameter args are not exactly the enclosing parameter bvars.
/// - [`InductiveError::IndexArgMentionsInductive`] — a block application's
///   index args mention a block name.
/// - [`InductiveError::InvalidInductiveOccurrence`] — any other embedded
///   occurrence (wrong arity, under/over-application, non-block-head core,
///   head level-list mismatch).
pub(crate) fn validate_inductive_strict(decl: &InductiveDecl) -> Result<(), InductiveError> {
    let p = decl.num_params;
    let block: Vec<&Name> = decl.types.iter().map(|t| &t.name).collect();

    // Per-member index counts; underflow = malformed former (design §5.5,
    // replaces the masking saturating_sub).
    let mut num_indices: Vec<u32> = Vec::with_capacity(decl.types.len());
    for member in &decl.types {
        let arity = count_pi_args(&member.type_);
        num_indices.push(arity.checked_sub(p).ok_or(InductiveError::InvalidParams)?);
    }

    // The exact level list every block-member occurrence must carry.
    let expected_levels: Vec<Level> = decl
        .level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect();

    let ctx = StrictCtx {
        decl,
        block: &block,
        num_indices: &num_indices,
        expected_levels: &expected_levels,
        p,
    };

    for (member_idx, member) in decl.types.iter().enumerate() {
        for ctor in &member.constructors {
            ctx.check_ctor(ctor, member_idx)?;
        }
    }
    Ok(())
}

struct StrictCtx<'a> {
    decl: &'a InductiveDecl,
    block: &'a [&'a Name],
    num_indices: &'a [u32],
    expected_levels: &'a [Level],
    p: u32,
}

impl StrictCtx<'_> {
    fn mentions_block(&self, e: &Expr) -> bool {
        self.block.iter().any(|n| mentions_name(e, n))
    }

    fn check_ctor(
        &self,
        ctor: &super::Constructor,
        member_idx: usize,
    ) -> Result<(), InductiveError> {
        // Walk the leading Pi binders tracking depth `t`; field domains
        // (binder index >= p) get the strict occurrence check.
        let mut cursor: &Expr = &ctor.type_;
        let mut t: u32 = 0;
        while let ExprKind::Pi(_, domain, body) = &cursor.kind {
            if t >= self.p {
                self.check_field(&ctor.name, domain, t)?;
            }
            cursor = body;
            t += 1;
        }

        // Return type: the HIT `CubicalPath` shape is validated by the
        // lenient pass's dedicated gate (validate_path_ctor_return_type);
        // everything else must be a valid application of the ctor's OWN
        // member.
        let return_type = get_return_type(&ctor.type_);
        if matches!(&return_type.kind, ExprKind::CubicalPath { .. }) {
            return Ok(());
        }
        self.check_valid_ind_app(&ctor.name, return_type, t, Some(member_idx))
    }

    /// Lean `check_positivity` (inductive.cpp:388-405), syntactic: a field
    /// may mention the block only along its rightmost Pi spine, ending in a
    /// valid inductive application.
    fn check_field(&self, ctor_name: &Name, field: &Expr, t: u32) -> Result<(), InductiveError> {
        if !self.mentions_block(field) {
            return Ok(());
        }
        match &field.kind {
            ExprKind::Pi(_, domain, body) => {
                if let Some(bad) = self.block.iter().find(|n| mentions_name(domain, n)) {
                    return Err(InductiveError::NonPositive(
                        (*bad).clone(),
                        ctor_name.clone(),
                    ));
                }
                self.check_field(ctor_name, body, t + 1)
            }
            _ => self.check_valid_ind_app(ctor_name, field, t, None),
        }
    }

    /// Lean `is_valid_ind_app` (inductive.cpp:338-357) in de Bruijn terms at
    /// depth `t`. `pinned_member`: for return types, the application must be
    /// of the ctor's own member; for fields, any block member qualifies.
    fn check_valid_ind_app(
        &self,
        ctor_name: &Name,
        e: &Expr,
        t: u32,
        pinned_member: Option<usize>,
    ) -> Result<(), InductiveError> {
        let head = e.get_app_fn();
        let ExprKind::Const(head_name, levels) = &head.kind else {
            return Err(self.invalid_occurrence(ctor_name, 0));
        };
        let member_idx = match pinned_member {
            Some(idx) => {
                if head_name != self.block[idx] {
                    return Err(InductiveError::ConstructorReturnType(
                        ctor_name.clone(),
                        self.block[idx].clone(),
                    ));
                }
                idx
            }
            None => match self.block.iter().position(|n| *n == head_name) {
                Some(idx) => idx,
                None => return Err(self.invalid_occurrence(ctor_name, 0)),
            },
        };

        // Check 1 (head levels): exactly the declaration's level params.
        if levels.as_slice() != self.expected_levels {
            return Err(self.invalid_occurrence(ctor_name, 0));
        }

        let args = e.get_app_args();
        // Check 2 (exact arity, per member).
        let expected_arity = self.p as usize + self.num_indices[member_idx] as usize;
        if args.len() != expected_arity {
            return Err(self.invalid_occurrence(ctor_name, args.len() as u32));
        }
        // Check 3 (param args are exactly the enclosing param bvars).
        for i in 0..self.p {
            let expected = Expr::bvar(t - 1 - i);
            if *args[i as usize] != expected {
                return Err(InductiveError::ConstructorParamMismatch {
                    ctor_name: ctor_name.clone(),
                    ind_name: self.block[member_idx].clone(),
                    param_idx: i,
                });
            }
        }
        // Check 4 (index args block-free — lean4#2125).
        for (pos, arg) in args.iter().enumerate().skip(self.p as usize) {
            if let Some(bad) = self.block.iter().find(|n| mentions_name(arg, n)) {
                return Err(InductiveError::IndexArgMentionsInductive {
                    ctor_name: ctor_name.clone(),
                    ind_name: (*bad).clone(),
                    index_pos: (pos - self.p as usize) as u32,
                });
            }
        }
        Ok(())
    }

    fn invalid_occurrence(&self, ctor_name: &Name, arg_idx: u32) -> InductiveError {
        InductiveError::InvalidInductiveOccurrence {
            ctor_name: ctor_name.clone(),
            ind_name: self.decl.types[0].name.clone(),
            arg_idx,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Constructor, InductiveDecl, InductiveError, InductiveType};
    use super::validate_inductive_strict;
    use crate::expr::{BinderInfo, Expr, ExprKind};
    use crate::level::Level;
    use crate::name::Name;

    fn sort_param(u: &str) -> Expr {
        Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string(u))))
    }

    fn t_at(u: &str) -> Expr {
        Expr::const_(
            Name::from_string("T"),
            vec![Level::param(Name::from_string(u))],
        )
    }

    /// `T.{u} (α : Type u) | mk : (T α → T α) → T α` — reflexive field with
    /// exact param spines everywhere: accepted.
    #[test]
    fn test_strict_accepts_reflexive_exact_spine() {
        // mk : Π (α : Type u) (f : Sort 0 → T α). T α — the classic
        // reflexive shape. Inside the field, the core sits under the field's
        // own Pi binder: binders crossed = α (1) + x (1) = 2, so α = BVar(1).
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(
                    BinderInfo::Default,
                    Expr::from_kind(ExprKind::Sort(Level::zero())),
                    Expr::app(t_at("u"), Expr::bvar(1)),
                ),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        validate_inductive_strict(&decl)
            .expect("reflexive field with exact param spine must be accepted");
    }

    /// Non-uniform occurrence `T Nat`-style (`T (Sort 0)` here) in a `T α`
    /// block: the §5.3a hole, now rejected.
    #[test]
    fn test_strict_rejects_non_uniform_field() {
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(t_at("u"), Expr::from_kind(ExprKind::Sort(Level::zero()))),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        let err = validate_inductive_strict(&decl)
            .expect_err("non-uniform block occurrence in a field must be rejected");
        assert!(
            matches!(
                err,
                InductiveError::ConstructorParamMismatch { param_idx: 0, .. }
            ),
            "expected param-spine mismatch, got {err:?}"
        );
    }

    /// Under-applied bare `T` in a field of a `p=1` block: rejected (wrong
    /// arity — Lean check 2).
    #[test]
    fn test_strict_rejects_under_applied_field() {
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                t_at("u"),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        let err = validate_inductive_strict(&decl)
            .expect_err("under-applied block occurrence must be rejected");
        assert!(
            matches!(err, InductiveError::InvalidInductiveOccurrence { .. }),
            "expected InvalidInductiveOccurrence, got {err:?}"
        );
    }

    /// Container-buried occurrence `F (T α)` with a non-block head `F`:
    /// rejected (post-transform, containers have been eliminated — a
    /// surviving one is a real violation).
    #[test]
    fn test_strict_rejects_non_block_head_core() {
        let f = Expr::const_(Name::from_string("F"), Vec::<Level>::new());
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(f, Expr::app(t_at("u"), Expr::bvar(0))),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        let err = validate_inductive_strict(&decl)
            .expect_err("block occurrence under a non-block head must be rejected");
        assert!(
            matches!(err, InductiveError::InvalidInductiveOccurrence { .. }),
            "expected InvalidInductiveOccurrence, got {err:?}"
        );
    }

    /// Head level-list mismatch: `T@{0}` in a `T.{u}` block field: rejected
    /// (Lean check 1 — the head must carry exactly the decl's level params).
    #[test]
    fn test_strict_rejects_wrong_head_levels() {
        let t_at_zero = Expr::const_(Name::from_string("T"), vec![Level::zero()]);
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(t_at_zero, Expr::bvar(0)),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        let err =
            validate_inductive_strict(&decl).expect_err("head level mismatch must be rejected");
        assert!(
            matches!(err, InductiveError::InvalidInductiveOccurrence { .. }),
            "expected InvalidInductiveOccurrence, got {err:?}"
        );
    }

    /// Negative occurrence (block in a field's Pi domain): rejected with
    /// NonPositive, same as the lenient pass.
    #[test]
    fn test_strict_rejects_negative_occurrence() {
        let mk = Expr::pi(
            BinderInfo::Default,
            sort_param("u"),
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(t_at("u"), Expr::bvar(0)),
                    Expr::from_kind(ExprKind::Sort(Level::zero())),
                ),
                Expr::app(t_at("u"), Expr::bvar(1)),
            ),
        );
        let decl = InductiveDecl {
            level_params: vec![Name::from_string("u")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("T"),
                type_: Expr::pi(BinderInfo::Default, sort_param("u"), sort_param("u")),
                constructors: vec![Constructor {
                    name: Name::from_string("T.mk"),
                    type_: mk,
                }],
            }],
        };
        let err =
            validate_inductive_strict(&decl).expect_err("negative occurrence must be rejected");
        assert!(
            matches!(err, InductiveError::NonPositive(..)),
            "expected NonPositive, got {err:?}"
        );
    }
}
