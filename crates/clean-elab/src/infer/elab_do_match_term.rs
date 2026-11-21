// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `do`-block `match` lowered through the term-level `match` compiler.
//!
//! Lean compiles a `doMatch` to an ordinary `match` term whose alternatives
//! are the arms' code blocks (`ToTerm.matchToTerm`, `src/Lean/Elab/Do.lean`).
//! Clean's do-match lowering builds its own `casesOn` and covers only some
//! pattern shapes: three or more discriminants lost their pattern bindings
//! (G42), a constructor pattern under a first-column split was reported
//! non-exhaustive (G35), and a literal pattern on a non-`Nat` scrutinee was
//! refused (G51). The term compiler handles each of these for a term
//! `match`. A do-match of such a shape whose arms carry no control flow the
//! enclosing block must thread (`break`, `continue`, a reassignment, or a
//! `return` that is not the arm's last element) is therefore elaborated as
//! `match d₁, …, dₙ with | p̄ => do arm | …`, Lean's own reading, with every
//! arm a nested `do` block in the block's monad.

use super::elab_do_control::{has_top_level_non_terminal_return, infer_control_info_seq};
use super::elab_do_mut::collect_do_mut_var_names;
use super::*;
use clean_parser::SurfaceMatchArm;

impl<'a> ElabCtx<'a> {
    /// Whether this do-match is lowered through the term `match` compiler.
    pub(super) fn do_match_term_route_applies(
        &mut self,
        discrs: &[SurfaceExpr],
        arms: &[DoMatchArm],
    ) -> bool {
        // The enclosing block threads nothing through the arms: no mutable
        // state lane, no loop accumulator, no transformer stack.
        if self.do_pure_state
            || self.do_loop_ctx.is_some()
            || self.do_control_stack.is_some()
            || self.do_wrapped_monad.is_some()
        {
            return false;
        }
        if Self::do_match_has_q_patterns(arms)
            || arms.iter().any(|arm| arm.patterns.len() != discrs.len())
        {
            return false;
        }
        let shape = discrs.len() >= 2
            || arms
                .iter()
                .flat_map(|arm| arm.patterns.iter())
                .any(|pattern| self.do_pattern_needs_term_route(pattern, false));
        shape
            && arms.iter().all(|arm| {
                let info = infer_control_info_seq(&arm.body);
                let mut muts = Vec::new();
                collect_do_mut_var_names(&arm.body, &mut muts);
                !info.breaks
                    && !info.continues
                    && info.reassigns.is_empty()
                    && muts.is_empty()
                    && !has_top_level_non_terminal_return(&arm.body)
            })
    }

    /// `match d₁, …, dₙ with | p₁, …, pₙ => do body | …` as a term, at the
    /// block's expected type (`statement` = the match is followed by more
    /// elements: its arms are then `m Unit` actions, as an `if` statement's
    /// branches are).
    pub(super) fn elab_do_match_term_route(
        &mut self,
        discrs: &[SurfaceExpr],
        arms: &[DoMatchArm],
        statement: bool,
    ) -> Result<Expr, ElabError> {
        let (first, rest) = discrs.split_first().ok_or_else(|| {
            ElabError::InternalInvariant("do-match term route with no discriminant".into())
        })?;
        let scrutinee = fold_right(first.clone(), rest.to_vec(), |expr, acc| {
            let span = expr.span().merge(acc.span());
            SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(
                    span,
                    SurfaceName::global_path("Prod.mk"),
                )),
                vec![SurfaceArg::positional(expr), SurfaceArg::positional(acc)],
            )
        });
        let term_arms = arms
            .iter()
            .map(|arm| {
                let (first, rest) = arm.patterns.split_first().ok_or_else(|| {
                    ElabError::InternalInvariant("do-match arm with no pattern".into())
                })?;
                let pattern = fold_right(first.clone(), rest.to_vec(), |pat, acc| {
                    SurfacePattern::Ctor(SurfaceName::generated_path("Prod.mk"), vec![pat, acc])
                });
                Ok(SurfaceMatchArm {
                    span: arm.span,
                    pattern,
                    body: SurfaceExpr::Do(arm.span, arm.body.clone()),
                })
            })
            .collect::<Result<Vec<_>, ElabError>>()?;
        let span = arms
            .last()
            .map_or(first.span(), |arm| first.span().merge(arm.span));
        let term = SurfaceExpr::Match(span, None, Box::new(scrutinee), term_arms);
        let expected = if statement {
            self.do_monad_info.as_ref().map(|info| {
                Expr::app(
                    info.m.clone(),
                    Expr::const_(Name::from_string("Unit"), vec![]),
                )
            })
        } else {
            self.current_expected_type.clone()
        };
        let saved = self.current_expected_type.clone();
        let result = self.elaborate_with_expected_type(&term, expected);
        self.current_expected_type = saved;
        result
    }
    /// A field pattern can be a constructor application or a bare identifier
    /// that resolves to a constructor. Let the term match compile the complete
    /// field column in both cases, including all of its sibling alternatives.
    fn do_pattern_needs_term_route(&mut self, pattern: &SurfacePattern, field: bool) -> bool {
        match pattern {
            SurfacePattern::Var(name) => {
                field
                    && (name.is_relative_constructor()
                        || self.bare_pattern_name_is_constructor(name) == Some(true))
            }
            SurfacePattern::Ctor(_, fields) => {
                field
                    || fields
                        .iter()
                        .any(|p| self.do_pattern_needs_term_route(p, true))
            }
            SurfacePattern::Lit(lit) => {
                field || !matches!(lit, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_))
            }
            SurfacePattern::As(_, inner) => self.do_pattern_needs_term_route(inner, field),
            SurfacePattern::NumeralAdd(inner, _) => {
                field || self.do_pattern_needs_term_route(inner, field)
            }
            SurfacePattern::Or(a, b) => {
                self.do_pattern_needs_term_route(a, field)
                    || self.do_pattern_needs_term_route(b, field)
            }
            SurfacePattern::Wildcard
            | SurfacePattern::Inaccessible(_)
            | SurfacePattern::QPattern(_)
            | SurfacePattern::StructInst { .. }
            | SurfacePattern::Ellipsis => false,
        }
    }
}

fn fold_right<T>(first: T, rest: Vec<T>, mut f: impl FnMut(T, T) -> T) -> T {
    let mut items = rest;
    let Some(mut acc) = items.pop() else {
        return first;
    };
    while let Some(item) = items.pop() {
        acc = f(item, acc);
    }
    f(first, acc)
}
