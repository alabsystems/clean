// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Join points for a catch-all arm (RM1, K5 root blocker 1).
//!
//! The constructor-ordered lowering expands a trailing catch-all arm
//! (`| _ => body`, `| a, b => body`) into one minor premise per constructor
//! the earlier arms leave uncovered, and it elaborates `body` once per
//! expanded minor. A body that is itself a `match` with a catch-all is then
//! elaborated once per constructor at every level, so the work is the
//! product of the uncovered-constructor counts down the nesting:
//! `TrustIr.Pred.impliesFuel` (a two-discriminant match over nine
//! constructors, six catch-all levels deep) never finished.
//!
//! Lean elaborates every alternative exactly once, as a lambda over its
//! pattern variables that the matcher applies in each case
//! (`Lean/Meta/Match/Match.lean`, `mkMatcher` alternatives). This does the
//! same for the catch-all: the body is elaborated once as
//! `j : S → C := fun s => match s with | p => body` and the catch-all arm
//! becomes `| p => j p`. Each expanded minor then elaborates a two-node
//! application, and the emitted term is `let j := …; T.casesOn …`, whose
//! size is linear in the source.
//!
//! The rewrite is a definitional identity (zeta, then beta, gives the
//! expansion back), so no proof authority moves: the kernel re-checks the
//! emitted term like any other. It is applied only where it cannot change
//! what a branch sees:
//! - the motive is constant: the expected type is known, has no
//!   metavariable, and mentions no free variable of the discriminant;
//! - there is no discriminant hypothesis (`match h : e`) and no dependent
//!   motive in force;
//! - the discriminant is not the structural-recursion argument, whose minors
//!   carry the induction hypotheses a catch-all body may need;
//! - the catch-all pattern is irrefutable (variables, wildcards, and the
//!   parser's `Prod.mk` tuple of those), so `j p` re-reads exactly the value
//!   the arm matched;
//! - the body has control flow of its own (a `match`, `if`, `let` or `do`
//!   at its head), which is the only shape whose expansion compounds. This
//!   is a cost filter only: the rewrite is correct for any body.
//!
//! The rewritten match's own catch-all arm is `| p => j p`, which is itself
//! irrefutable and is lowered by this same entry. A catch-all whose body is
//! a call of the join binder is declined first, before any other gate
//! ([`JoinOutcome::JoinCall`]), so the rewrite never re-enters itself
//! whatever the cost filter says.
//!
//! If elaborating the join fails, or the join it produces does not have the
//! type `S → C` (an internal match left partial), every side effect is
//! rolled back and the match is lowered exactly as before.
//!
//! Each call ends in one [`JoinOutcome`]. Debug and test builds record it
//! per thread ([`take_join_outcomes`]), so a test can show which gate
//! declined a shape: every gate has a fixture that only it declines
//! (`tests/rm1_elab_fixes/join_point_gates.lean`).

use super::*;
use clean_parser::{Span, SurfaceArg};

/// How one attempt to lower a match through a join point ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum JoinOutcome {
    /// The catch-all was elaborated once and the match lowered through it.
    Applied,
    /// A single arm: nothing to share.
    SingleArm,
    /// The catch-all body is the rewrite's own `j p` call.
    JoinCall,
    /// A `match h : e` discriminant hypothesis is in force.
    DiscriminantHypothesis,
    /// An enclosing match's dependent motive is in force.
    DependentMotive,
    /// The catch-all pattern can fail to match.
    RefutableCatchAll,
    /// The catch-all body has no control flow of its own (cost filter).
    PlainBody,
    /// There is no expected type.
    ExpectedTypeUnknown,
    /// The expected type still has a metavariable (or a loose bound
    /// variable), as does the discriminant's type.
    ExpectedTypeOpen,
    /// The expected type mentions a free variable of the discriminant.
    MotiveMentionsDiscriminant,
    /// The discriminant is the structural-recursion argument or an
    /// induction-hypothesis field.
    RecursionArgument,
    /// Elaborating the join failed; the old lowering runs.
    JoinElabFailed,
    /// The join elaborated but is not of type `S → C`; the old lowering runs.
    JoinIllTyped,
    /// Lowering the rewritten match failed; the old lowering runs.
    MatchElabFailed,
}

#[cfg(any(test, debug_assertions))]
thread_local! {
    static JOIN_OUTCOMES: RefCell<Vec<JoinOutcome>> =
        const { RefCell::new(Vec::new()) };
}

/// Record `outcome` on this thread (debug and test builds only).
fn record(outcome: JoinOutcome) {
    #[cfg(any(test, debug_assertions))]
    JOIN_OUTCOMES.with(|outcomes| outcomes.borrow_mut().push(outcome));
    #[cfg(not(any(test, debug_assertions)))]
    let _ = outcome;
}

/// The join-point outcomes recorded on this thread since the last call, in
/// order (test seam).
#[cfg(any(test, debug_assertions))]
pub fn take_join_outcomes() -> Vec<JoinOutcome> {
    JOIN_OUTCOMES.with(|outcomes| std::mem::take(&mut *outcomes.borrow_mut()))
}

/// Binder name of the join point. `✝` cannot appear in a source identifier,
/// so no user name can capture or shadow it.
const JOIN_NAME: &str = MATCH_JOIN_BINDER;
/// Binder name of the join point's argument.
const JOIN_ARG_NAME: &str = "_match_join_arg✝";

/// True for a pattern that matches every value of its type: a variable, a
/// wildcard, or the parser's right-nested `Prod.mk` tuple of those.
/// Patterns reach here after `normalize_match_pattern_names`, so a `Var` is
/// a binder, never a nullary constructor.
fn irrefutable(pattern: &SurfacePattern) -> bool {
    match pattern {
        SurfacePattern::Var(_) | SurfacePattern::Wildcard => true,
        SurfacePattern::Ctor(name, args) => {
            name.same_syntax(&SurfaceName::generated_path("Prod.mk"))
                && args.len() == 2
                && args.iter().all(irrefutable)
        }
        _ => false,
    }
}

/// The pattern with every wildcard replaced by a fresh variable, so the arm
/// can rebuild the value it matched.
fn name_wildcards(pattern: &SurfacePattern, next: &mut usize) -> SurfacePattern {
    match pattern {
        SurfacePattern::Wildcard => {
            let name = SurfaceName::generated_path(&format!("_match_join_w✝{next}"));
            *next += 1;
            SurfacePattern::Var(name)
        }
        SurfacePattern::Ctor(name, args) => SurfacePattern::Ctor(
            name.clone(),
            args.iter().map(|arg| name_wildcards(arg, next)).collect(),
        ),
        other => other.clone(),
    }
}

/// The value an irrefutable, wildcard-free pattern matched.
fn pattern_value(pattern: &SurfacePattern) -> SurfaceExpr {
    match pattern {
        SurfacePattern::Var(name) => SurfaceExpr::Ident(Span::dummy(), name.clone()),
        // Only the tuple constructor reaches here (`irrefutable`).
        SurfacePattern::Ctor(_, args) => SurfaceExpr::App(
            Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                Span::dummy(),
                SurfaceName::global_path("Prod.mk"),
            )),
            args.iter()
                .map(|arg| SurfaceArg {
                    span: Span::dummy(),
                    expr: pattern_value(arg),
                    name: None,
                })
                .collect(),
        ),
        // `irrefutable` admits no other shape and `name_wildcards` removed
        // every wildcard.
        _ => SurfaceExpr::Hole(Span::dummy()),
    }
}

/// A body whose expansion compounds: it has control flow of its own.
fn body_branches(body: &SurfaceExpr) -> bool {
    match body {
        SurfaceExpr::Paren(_, inner) => body_branches(inner),
        SurfaceExpr::Match(..)
        | SurfaceExpr::If(..)
        | SurfaceExpr::IfLet(..)
        | SurfaceExpr::IfDecidable(..)
        | SurfaceExpr::Let(..)
        | SurfaceExpr::Have(..)
        | SurfaceExpr::LetPattern(..)
        | SurfaceExpr::Do(..) => true,
        _ => false,
    }
}

/// Is `body` a call of the join binder: the `| p => j p` arm the rewrite
/// itself emits?
fn is_join_call(body: &SurfaceExpr) -> bool {
    match body {
        SurfaceExpr::Paren(_, inner) => is_join_call(inner),
        SurfaceExpr::App(_, f, _) => {
            matches!(f.as_ref(), SurfaceExpr::Ident(_, n) if n.name().to_string() == JOIN_NAME)
        }
        _ => false,
    }
}

/// Does the surface expression mention `name` as an identifier? Used only to
/// keep the recursion argument's own match on the old lowering; a false
/// positive just declines the rewrite.
fn mentions_ident(expr: &SurfaceExpr, name: &SurfaceName) -> bool {
    match expr {
        SurfaceExpr::Ident(_, n) => n.name() == name.name(),
        SurfaceExpr::Paren(_, inner) => mentions_ident(inner, name),
        SurfaceExpr::App(_, f, args) => {
            mentions_ident(f, name) || args.iter().any(|a| mentions_ident(&a.expr, name))
        }
        // Anything else: say yes, so the rewrite declines.
        _ => true,
    }
}

impl<'a> ElabCtx<'a> {
    /// Lower `arms` with its catch-all arm elaborated once as a join point,
    /// or `Ok(None)` when the rewrite does not apply (see the module docs).
    /// Every call records its [`JoinOutcome`].
    pub(in crate::infer) fn try_lower_match_with_join_point(
        &mut self,
        scrutinee_expr: &Expr,
        scrutinee_ty: &Expr,
        scrutinee_surface: Option<&SurfaceExpr>,
        discriminant_hypothesis: bool,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Option<Expr>, ElabError> {
        let result = self.join_point_lowering(
            scrutinee_expr,
            scrutinee_ty,
            scrutinee_surface,
            discriminant_hypothesis,
            arms,
        );
        match result {
            Ok(Ok(lowered)) => {
                record(JoinOutcome::Applied);
                Ok(Some(lowered))
            }
            Ok(Err(declined)) => {
                record(declined);
                Ok(None)
            }
            Err(e) => Err(e),
        }
    }

    /// The join-point lowering, or the [`JoinOutcome`] that declined it.
    fn join_point_lowering(
        &mut self,
        scrutinee_expr: &Expr,
        scrutinee_ty: &Expr,
        scrutinee_surface: Option<&SurfaceExpr>,
        discriminant_hypothesis: bool,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Result<Expr, JoinOutcome>, ElabError> {
        use JoinOutcome as O;
        let Some((catch_all, earlier)) = arms.split_last() else {
            return Ok(Err(O::SingleArm));
        };
        if earlier.is_empty() {
            return Ok(Err(O::SingleArm));
        }
        if is_join_call(&catch_all.body) {
            return Ok(Err(O::JoinCall));
        }
        if discriminant_hypothesis {
            return Ok(Err(O::DiscriminantHypothesis));
        }
        if self.match_dependent_motive.is_some() {
            return Ok(Err(O::DependentMotive));
        }
        if !irrefutable(&catch_all.pattern) {
            return Ok(Err(O::RefutableCatchAll));
        }
        if !body_branches(&catch_all.body) {
            return Ok(Err(O::PlainBody));
        }
        let Some(branch_ty) = self.current_expected_type.clone() else {
            return Ok(Err(O::ExpectedTypeUnknown));
        };
        let branch_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&branch_ty));
        // An elaborator metavariable is a tagged `FVar`, which the kernel's
        // `has_expr_mvar_quick` flag never sees (`MetaState::expr_has_meta`).
        let scrutinee_ty_now = self.metas.instantiate(scrutinee_ty);
        if MetaState::expr_has_meta(&branch_ty)
            || branch_ty.has_level_mvar_quick()
            || branch_ty.has_loose_bvars_quick()
            || MetaState::expr_has_meta(&scrutinee_ty_now)
        {
            return Ok(Err(O::ExpectedTypeOpen));
        }
        let scrutinee_fvars = crate::tactic::hypothesis::collect_fvars(scrutinee_expr);
        if crate::tactic::hypothesis::collect_fvars(&branch_ty)
            .iter()
            .any(|fvar| scrutinee_fvars.contains(fvar))
        {
            return Ok(Err(O::MotiveMentionsDiscriminant));
        }
        if let Some(ctx) = self.recursive_def_ctx.as_ref() {
            let on_recursion_arg = match scrutinee_surface {
                Some(surface) => mentions_ident(surface, &ctx.decreasing_arg_name),
                None => true,
            };
            let on_ih_field = ctx.ih_map.keys().any(|fvar| scrutinee_fvars.contains(fvar));
            if on_recursion_arg || on_ih_field {
                return Ok(Err(O::RecursionArgument));
            }
        }

        let mut next = 0;
        let pattern = name_wildcards(&catch_all.pattern, &mut next);
        let join_arm = clean_parser::SurfaceMatchArm {
            span: catch_all.span,
            pattern: pattern.clone(),
            body: catch_all.body.clone(),
        };
        let join_name = SurfaceName::generated_path(JOIN_NAME);
        let leaf_arm = clean_parser::SurfaceMatchArm {
            span: catch_all.span,
            pattern: pattern.clone(),
            body: SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), join_name.clone())),
                vec![SurfaceArg {
                    span: Span::dummy(),
                    expr: pattern_value(&pattern),
                    name: None,
                }],
            ),
        };
        let mut rewritten: Vec<clean_parser::SurfaceMatchArm> = earlier.to_vec();
        rewritten.push(leaf_arm);

        // The scope rolls back every side effect unless the closure returns
        // `Ok(Some(_))`; a decline names its outcome through `declined`.
        let mut declined = O::JoinElabFailed;
        let lowered = self.with_optional_temporary_local_scope(|this| {
            // j := fun s => match s with | p => body   (elaborated once)
            let arg = this.push_local(
                SurfaceName::generated_path(JOIN_ARG_NAME),
                scrutinee_ty.clone(),
            );
            let saved = this.current_expected_type.replace(branch_ty.clone());
            let join_body = this.elab_match_with_scrutinee_hyp(
                None,
                Expr::fvar(arg),
                scrutinee_ty.clone(),
                None,
                std::slice::from_ref(&join_arm),
            );
            this.current_expected_type = saved;
            this.pop_local();
            let Ok(join_body) = join_body else {
                declined = O::JoinElabFailed;
                return Ok(None);
            };
            let join_body = this.metas.instantiate(&join_body);
            let join_val = Expr::lam(
                BinderInfo::Default,
                scrutinee_ty.clone(),
                join_body.abstract_fvar(arg),
            );
            let join_ty = Expr::arrow(scrutinee_ty.clone(), branch_ty.clone());
            // The join must have exactly the type its call sites assume. A
            // lowering that leaves an internal match partial (the decision
            // tree's default rows of a non-exhaustive match) yields a
            // casesOn still waiting for minors; decline, so the old lowering
            // reports the match as non-exhaustive instead of the kernel
            // refusing an ill-typed `let`.
            let typed = this
                .infer_type(&join_val)
                .is_ok_and(|ty| this.is_def_eq(&ty, &join_ty));
            if !typed {
                declined = O::JoinIllTyped;
                return Ok(None);
            }

            // The match itself, with the catch-all arm calling `j`.
            let join = this.push_local(join_name.clone(), join_ty.clone());
            let saved = this.current_expected_type.replace(branch_ty.clone());
            let lowered = this.elab_match_with_scrutinee_hyp(
                None,
                scrutinee_expr.clone(),
                scrutinee_ty.clone(),
                scrutinee_surface,
                &rewritten,
            );
            this.current_expected_type = saved;
            this.pop_local();
            let Ok(lowered) = lowered else {
                declined = O::MatchElabFailed;
                return Ok(None);
            };
            let lowered = this.metas.instantiate(&lowered);
            Ok(Some(Expr::let_named(
                join_name.name().clone(),
                join_ty,
                join_val,
                lowered.abstract_fvar(join),
                false,
            )))
        })?;
        Ok(lowered.ok_or(declined))
    }
}
