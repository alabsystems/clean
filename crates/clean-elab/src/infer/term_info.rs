// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-info observations with the actual elaboration parent relationships.

use super::*;
use crate::tactic::{LocalDecl, ProofState};
use crate::term_info::{SortGoalId, SourceInfo, TermContext, TermInfoCapture};
use clean_parser::{SurfaceBinder, SurfaceTactic};
use std::collections::HashSet;

pub(super) struct InfoFrame {
    id: u64,
    parent_id: Option<u64>,
    depth: usize,
    span: clean_parser::Span,
    application_head: Option<clean_parser::Span>,
}

#[derive(Clone)]
enum PendingTerm {
    Elaborated {
        expr: Expr,
        expected_type: Option<Expr>,
        unresolved_sort_goal: Option<SortGoalId>,
        locals: Vec<LocalDecl>,
        is_binder: bool,
    },
    Resolved(TermContext),
    Other,
}

pub(super) struct PendingInfo {
    frame: InfoFrame,
    is_variable: bool,
    is_partial: bool,
    term: PendingTerm,
}

impl ElabCtx<'_> {
    /// Commit the outer observation from an accepted typed body check after
    /// implicit insertion or coercion has produced its checked value. Child
    /// observations retain their actual elaboration targets.
    pub(super) fn commit_checked_body_info(
        &mut self,
        mark: usize,
        span: clean_parser::Span,
        expr: &Expr,
        expected: &Expr,
    ) {
        let Some(info) = self
            .term_contexts
            .get_mut(mark..)
            .and_then(|infos| infos.last_mut())
        else {
            return;
        };
        if info.frame.span != span {
            return;
        }
        if let PendingTerm::Elaborated {
            expr: observed,
            expected_type,
            ..
        } = &mut info.term
        {
            *observed = expr.clone();
            *expected_type = Some(expected.clone());
            info.is_variable =
                matches!(expr.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_none());
        }
    }

    /// Observe the real type-position constraint without allocating producer
    /// metavariables or changing how the expression itself is elaborated.
    pub(super) fn elaborate_type_observing(
        &mut self,
        surface: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let Some(capture) = &self.term_info_capture else {
            return self.elaborate(surface);
        };
        let constraint = capture.fresh_sort_goal();
        let mark = self.term_contexts.len();
        let result = self.elaborate(surface);
        // Lean's literal Prop/Sort/Type elaborators ignore their expected
        // sort; unlike identifiers they leave that constraint unresolved.
        // Parentheses retain the same expected constraint on their inner term.
        let mut inner = surface;
        let mut spans = vec![inner.span()];
        while let SurfaceExpr::Paren(_, term) = inner {
            inner = term;
            spans.push(inner.span());
        }
        if matches!(inner, SurfaceExpr::Universe(..)) {
            if let Some(infos) = self.term_contexts.get_mut(mark..) {
                for info in infos {
                    if spans.contains(&info.frame.span) {
                        if let PendingTerm::Elaborated {
                            unresolved_sort_goal,
                            ..
                        } = &mut info.term
                        {
                            *unresolved_sort_goal = constraint;
                        }
                    }
                }
            }
        }
        result
    }

    pub(crate) fn set_term_info_capture(&mut self, capture: Option<TermInfoCapture>) {
        self.term_info_capture = capture;
        self.term_contexts.clear();
        self.term_info_stack.clear();
    }

    fn begin_info(
        &mut self,
        span: clean_parser::Span,
        application_head: Option<clean_parser::Span>,
    ) -> Option<InfoFrame> {
        let id = self.term_info_capture.as_ref()?.fresh_id();
        let frame = InfoFrame {
            id,
            parent_id: self.term_info_stack.last().copied(),
            depth: self.term_info_stack.len(),
            span,
            application_head,
        };
        self.term_info_stack.push(id);
        Some(frame)
    }

    fn end_info(&mut self, frame: &InfoFrame) {
        self.term_info_stack.truncate(frame.depth);
    }

    fn observed_locals(&self) -> Vec<LocalDecl> {
        self.locals
            .iter()
            .map(|(name, fvar, ty)| LocalDecl {
                binder_info: self.locals.binder_info(*fvar),
                fvar: *fvar,
                name: self
                    .term_local_display_names
                    .get(fvar)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
                ty: ty.clone(),
                value: self.locals.let_value(*fvar).cloned(),
            })
            .collect()
    }

    pub(super) fn elaborate_capturing_term(
        &mut self,
        surface: &SurfaceExpr,
        expected_type: Option<Expr>,
        elaborate: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        let Some(frame) = self.begin_info(surface.span(), None) else {
            return elaborate(self);
        };
        // A complete application and its written head are distinct source
        // ranges. Keep both tied to the actual applied value. This frame must
        // enclose the head and argument elaborations: it supersedes the partial
        // function observation at the head without hiding argument observations.
        // Parenthesized heads remain separate authored function contexts.
        let head_frame = match surface {
            SurfaceExpr::App(_, head, _)
                if matches!(
                    head.as_ref(),
                    SurfaceExpr::Ident(..) | SurfaceExpr::Proj(..)
                ) =>
            {
                let span = head.span();
                if frame.span.start <= span.start
                    && span.start < span.end
                    && span.end <= frame.span.end
                {
                    self.begin_info(span, Some(span))
                } else {
                    None
                }
            }
            _ => None,
        };
        let locals = self.observed_locals();
        let result = elaborate(self);
        self.end_info(&frame);
        let is_variable = matches!(&result, Ok(expr) if matches!(expr.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_none()));
        let term = match &result {
            Ok(expr)
                if !matches!(
                    surface,
                    SurfaceExpr::ByTactic(..) | SurfaceExpr::SyntheticSorry(..)
                ) && frame.span.start < frame.span.end =>
            {
                PendingTerm::Elaborated {
                    expr: expr.clone(),
                    expected_type,
                    unresolved_sort_goal: None,
                    locals,
                    is_binder: false,
                }
            }
            _ => PendingTerm::Other,
        };
        // Ordinary errors keep their real child observations. Speculative
        // alternatives are discarded by the existing local-scope checkpoint.
        if let Some(head_frame) = head_frame {
            self.term_contexts.push(PendingInfo {
                frame: head_frame,
                is_variable,
                is_partial: result.is_err(),
                term: term.clone(),
            });
        }
        self.term_contexts.push(PendingInfo {
            frame,
            is_variable,
            is_partial: result.is_err(),
            term,
        });
        result
    }

    pub(super) fn capture_binder_info(&mut self, binder: &SurfaceBinder, fvar: FVarId) {
        self.locals
            .set_binder_info(fvar, convert_binder_info(binder.info).into());
        if self.term_info_capture.is_none() || binder.span.start >= binder.span.end {
            return;
        }
        let mut locals = self.observed_locals();
        let Some(index) = locals.iter().position(|local| local.fvar == fvar) else {
            return;
        };
        locals.truncate(index + 1);
        if let Some(frame) = self.begin_info(binder.span, None) {
            self.end_info(&frame);
            self.term_contexts.push(PendingInfo {
                frame,
                is_variable: true,
                is_partial: false,
                term: PendingTerm::Elaborated {
                    expr: Expr::fvar(fvar),
                    expected_type: None,
                    unresolved_sort_goal: None,
                    locals,
                    is_binder: true,
                },
            });
        }
    }

    pub(super) fn begin_tactic_info(&mut self, span: clean_parser::Span) -> Option<InfoFrame> {
        self.begin_info(span, None)
    }

    pub(super) fn end_tactic_info(&mut self, frame: Option<InfoFrame>, is_partial: bool) {
        if let Some(frame) = frame {
            self.end_info(&frame);
            self.term_contexts.push(PendingInfo {
                frame,
                is_variable: false,
                is_partial,
                term: PendingTerm::Other,
            });
        }
    }

    pub(super) fn intro_info_before(
        &self,
        ps: &ProofState,
        tac: &SurfaceTactic,
    ) -> Option<HashSet<FVarId>> {
        if self.term_info_capture.is_none()
            || !matches!(tac, SurfaceTactic::Named { name, .. } if name == "intro" || name == "intros")
        {
            return None;
        }
        Some(
            ps.current_goal()?
                .local_ctx
                .iter()
                .map(|local| local.fvar)
                .collect(),
        )
    }

    pub(super) fn capture_intro_binders(
        &mut self,
        ps: &ProofState,
        tac: &SurfaceTactic,
        before: Option<&HashSet<FVarId>>,
    ) {
        let (Some(before), SurfaceTactic::Named { args, .. }, Some(goal)) =
            (before, tac, ps.current_goal())
        else {
            return;
        };
        let introduced: Vec<_> = goal
            .local_ctx
            .iter()
            .enumerate()
            .filter(|(_, local)| !before.contains(&local.fvar))
            .collect();
        if introduced.len() != args.len() {
            return;
        }
        for (arg, (index, local)) in args.iter().zip(introduced) {
            let SurfaceExpr::Ident(span, name) = arg else {
                continue;
            };
            if name != &local.name || span.start >= span.end {
                continue;
            }
            let locals: Vec<_> = goal.local_ctx[..=index]
                .iter()
                .map(|local| LocalDecl {
                    binder_info: local.binder_info,
                    fvar: local.fvar,
                    name: self
                        .term_local_display_names
                        .get(&local.fvar)
                        .cloned()
                        .unwrap_or_else(|| local.name.clone()),
                    ty: ps.instantiate_for_kernel(&local.ty),
                    value: local
                        .value
                        .as_ref()
                        .map(|value| ps.instantiate_for_kernel(value)),
                })
                .collect();
            let type_ = ps.instantiate_for_kernel(&local.ty);
            if let Some(frame) = self.begin_info(*span, None) {
                self.end_info(&frame);
                self.term_contexts.push(PendingInfo {
                    frame,
                    is_variable: true,
                    is_partial: false,
                    // This snapshot owns the tactic metavariable context. Never
                    // reinterpret its identities through ElabCtx's metas.
                    term: PendingTerm::Resolved(TermContext {
                        expr: Expr::fvar(local.fvar),
                        expected_type: None,
                        unresolved_sort_goal: None,
                        type_,
                        local_context: locals,
                        is_binder: true,
                    }),
                });
            }
        }
    }

    fn finalize_observed_term(&self, term: PendingTerm) -> Option<TermContext> {
        let (expr, expected_type, unresolved_sort_goal, locals, is_binder) = match term {
            PendingTerm::Elaborated {
                expr,
                expected_type,
                unresolved_sort_goal,
                locals,
                is_binder,
            } => (expr, expected_type, unresolved_sort_goal, locals, is_binder),
            PendingTerm::Resolved(term) => return Some(term),
            PendingTerm::Other => return None,
        };
        let instantiate =
            |expr: &Expr| self.metas.instantiate_levels(&self.metas.instantiate(expr));
        let expr = instantiate(&expr);
        let expected_type = expected_type.as_ref().map(instantiate);
        let local_context: Vec<_> = locals
            .into_iter()
            .map(|local| LocalDecl {
                binder_info: local.binder_info,
                fvar: local.fvar,
                name: local.name,
                ty: instantiate(&local.ty),
                value: local.value.as_ref().map(instantiate),
            })
            .collect();
        let type_ = if let Some(ty) = &expected_type {
            ty.clone()
        } else if let ExprKind::FVar(id) = expr.kind() {
            if let Some(meta) = MetaState::from_fvar(*id) {
                instantiate(&self.metas.get(meta)?.ty)
            } else {
                self.infer_observed_type(&expr, &local_context)?
            }
        } else {
            self.infer_observed_type(&expr, &local_context)?
        };
        Some(TermContext {
            expr,
            expected_type,
            unresolved_sort_goal,
            type_,
            local_context,
            is_binder,
        })
    }

    fn infer_observed_type(&self, expr: &Expr, context: &[LocalDecl]) -> Option<Expr> {
        let mut locals = LocalContext::new();
        for local in context {
            if let Some(value) = local.reduction_value() {
                locals.push_let_with_id(
                    local.fvar,
                    local.name.name().clone(),
                    local.ty.clone(),
                    value.clone(),
                );
            } else {
                locals.push_with_id(
                    local.fvar,
                    local.name.name().clone(),
                    local.ty.clone(),
                    local.binder_info,
                );
            }
        }
        TypeChecker::with_context_and_caches(self.env, locals, TcCaches::default())
            .infer_type_full(expr)
            .ok()
    }

    pub(crate) fn finish_term_info(&mut self) {
        let Some(capture) = self.term_info_capture.clone() else {
            return;
        };
        let pending = std::mem::take(&mut self.term_contexts);
        let infos = pending
            .into_iter()
            .map(|pending| {
                let was_term = matches!(
                    &pending.term,
                    PendingTerm::Elaborated { .. } | PendingTerm::Resolved(_)
                );
                let term = self.finalize_observed_term(pending.term);
                SourceInfo {
                    id: pending.frame.id,
                    parent_id: pending.frame.parent_id,
                    span: pending.frame.span,
                    application_head: pending.frame.application_head,
                    is_variable: pending.is_variable && term.is_some(),
                    is_partial: pending.is_partial || (was_term && term.is_none()),
                    term,
                }
            })
            .collect();
        capture.record(infos);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local_identity_context(env: &Environment) -> (ElabCtx<'_>, FVarId) {
        let mut ctx = ElabCtx::new(env);
        let carrier = ctx.push_local(
            SurfaceName::component("A", false),
            Expr::sort(Level::succ(Level::zero())),
        );
        ctx.push_local(SurfaceName::component("x", false), Expr::fvar(carrier));
        (ctx, carrier)
    }

    #[test]
    fn sort_constraints_remain_separate_from_inferred_types() {
        let env = Environment::new();
        let surface = clean_parser::parse_expr("Type").expect("sort literal parses");
        let mut ctx = ElabCtx::new(&env);
        let capture = TermInfoCapture::default();
        ctx.set_term_info_capture(Some(capture.clone()));
        let value = ctx
            .elaborate_type_observing(&surface)
            .expect("sort elaborates");
        let inferred =
            TypeChecker::with_context_and_caches(&env, LocalContext::new(), TcCaches::default())
                .infer_type_full(&value)
                .expect("the actual type is independently inferred");
        ctx.finish_term_info();
        let term = capture
            .take()
            .expect("observations available")
            .into_iter()
            .find_map(|info| info.term.filter(|term| term.unresolved_sort_goal.is_some()))
            .expect("type-position constraint recorded");
        assert_eq!(term.expr, value);
        assert_eq!(
            term.type_, inferred,
            "display constraints do not replace the inferred type"
        );
        assert!(term.expected_type.is_none());
        assert_eq!(term.render_goal(&env), "⊢ Sort ?u.1");
    }

    #[test]
    fn positional_projection_preserves_the_observed_head_range_and_goal() {
        let mut env = Environment::with_prelude();
        crate::elaborate_decl_and_register(
            &mut env,
            &clean_parser::parse_decl(
                "def Nat.takeReceiverLater (step : Bool) (n : Nat) : Nat := n",
            )
            .unwrap(),
        )
        .unwrap();
        let mut ctx = ElabCtx::new(&env);
        ctx.push_local(
            SurfaceName::component("n", false),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        let head = "n.takeReceiverLater";
        let capture = TermInfoCapture::default();
        ctx.set_term_info_capture(Some(capture.clone()));
        let source = format!("{head} true");
        let applied = ctx
            .elaborate(&clean_parser::parse_expr(&source).unwrap())
            .unwrap();
        assert!(matches!(applied.kind(), ExprKind::App(..)));
        ctx.finish_term_info();
        let contexts = capture.take().unwrap();
        // The normal plainTermGoal endpoint reports the applied Nat term
        // on the written projection range, distinct from the argument range.
        let recorded = contexts
            .iter()
            .filter(|info| info.span.start == 0 && info.span.end == head.len())
            .filter_map(|info| info.term.as_ref())
            .find(|term| term.expr == applied)
            .expect("the source range identifies the applied field term");
        assert_eq!(recorded.render_goal(&env), "n : Nat\n⊢ Nat");
        let full_application = contexts
            .iter()
            .find(|info| {
                info.span == clean_parser::Span::new(0, source.len())
                    && info.term.as_ref().is_some_and(|term| term.expr == applied)
            })
            .expect("the complete physical application remains observed");
        let applied_head = contexts
            .iter()
            .find(|info| {
                info.span == clean_parser::Span::new(0, head.len())
                    && info.term.as_ref().is_some_and(|term| term.expr == applied)
            })
            .expect("the applied head has its own source-info node");
        assert_eq!(applied_head.parent_id, Some(full_application.id));
        assert_eq!(applied_head.application_head, Some(applied_head.span));
        assert!(contexts.iter().any(|info| {
            info.span == clean_parser::Span::new(0, 1)
                && info.is_variable
                && info
                    .term
                    .as_ref()
                    .is_some_and(|term| term.render_goal(&env) == "n : Nat\n⊢ Nat")
        }));
        let argument = contexts
            .iter()
            .find(|info| {
                info.span == clean_parser::Span::new(head.len() + 1, source.len())
                    && info
                        .term
                        .as_ref()
                        .is_some_and(|term| term.render_goal(&env) == "n : Nat\n⊢ Bool")
            })
            .expect("the argument retains its own observed goal");
        let mut parent = argument.parent_id;
        let mut under_applied_head = false;
        for _ in 0..contexts.len() {
            let Some(id) = parent else { break };
            if id == applied_head.id {
                under_applied_head = true;
                break;
            }
            parent = contexts
                .iter()
                .find(|info| info.id == id)
                .unwrap()
                .parent_id;
        }
        assert!(under_applied_head);
    }

    #[test]
    fn expected_term_context_retains_actual_dependent_locals() {
        let env = Environment::new();
        let capture = TermInfoCapture::default();
        let mut ctx = ElabCtx::new(&env);
        ctx.set_term_info_capture(Some(capture.clone()));
        let text = "def identity (A : Type) (x : A) : A := x";
        ctx.elab_decl(&clean_parser::parse_decl(text).unwrap())
            .unwrap();
        ctx.finish_term_info();
        let contexts = capture.take().unwrap();
        let info = contexts
            .iter()
            .rev()
            .find(|info| info.span.start == text.rfind('x').unwrap())
            .expect("the actual body term was observed");
        assert_eq!(info.span.end, text.len());
        let term = info.term.as_ref().expect("body is a term node");
        assert_eq!(term.local_context.len(), 2);
        let carrier = term.local_context[0].fvar;
        assert_eq!(term.expected_type, Some(Expr::fvar(carrier)));
        assert_eq!(term.type_, Expr::fvar(carrier));
        assert_eq!(term.expr, Expr::fvar(term.local_context[1].fvar));
        assert_eq!(term.render_goal(&env), "A : Type\nx : A\n⊢ A");
    }

    #[test]
    fn inference_only_term_uses_its_type_in_the_captured_local_context() {
        let env = Environment::new();
        let (mut ctx, carrier) = local_identity_context(&env);
        let capture = TermInfoCapture::default();
        ctx.set_term_info_capture(Some(capture.clone()));
        let expr = ctx
            .elaborate(&clean_parser::parse_expr("x").unwrap())
            .unwrap();
        ctx.finish_term_info();
        let contexts = capture.take().unwrap();
        assert_eq!(contexts.len(), 1);
        let term = contexts[0].term.as_ref().unwrap();
        assert_eq!(term.expr, expr);
        assert!(term.expected_type.is_none());
        assert_eq!(term.type_, Expr::fvar(carrier));
        assert_eq!(term.render_goal(&env), "A : Type\nx : A\n⊢ A");
    }

    #[test]
    fn failed_speculative_scope_cannot_publish_a_successful_inner_term() {
        let env = Environment::new();
        let (mut ctx, _) = local_identity_context(&env);
        let capture = TermInfoCapture::default();
        ctx.set_term_info_capture(Some(capture.clone()));
        let expr = clean_parser::parse_expr("x").unwrap();
        let result: Result<(), ElabError> = ctx.with_local_scope_rollback(|ctx| {
            let candidate = ctx.elaborate(&expr)?;
            assert!(matches!(candidate.kind(), ExprKind::FVar(_)));
            Err(ElabError::Unsupported {
                feature: "deliberately rejected candidate".to_string(),
            })
        });
        assert!(result.is_err());
        ctx.finish_term_info();
        assert!(capture.take().unwrap().is_empty());
        let accepted = ctx.elaborate(&expr).unwrap();
        ctx.finish_term_info();
        let contexts = capture.take().unwrap();
        assert_eq!(contexts.len(), 1);
        assert_eq!(contexts[0].term.as_ref().unwrap().expr, accepted);
    }

    #[test]
    fn opt_in_observation_preserves_the_elaborated_definition() {
        let env = Environment::new();
        for text in [
            "def identity (A : Type) (x : A) : A := x",
            "def tactic_identity (A : Type) : A → A := by\n  intro x\n  exact x\n",
        ] {
            let decl = clean_parser::parse_decl(text).unwrap();
            let mut ordinary = ElabCtx::new(&env);
            let reference = ordinary.elab_decl(&decl).unwrap();
            assert!(ordinary.term_contexts.is_empty());
            let capture = TermInfoCapture::default();
            let mut observed = ElabCtx::new(&env);
            observed.set_term_info_capture(Some(capture.clone()));
            let actual = observed.elab_decl(&decl).unwrap();
            observed.finish_term_info();
            match (reference, actual) {
                (
                    ElabResult::Definition { ty, val, .. },
                    ElabResult::Definition {
                        ty: observed_ty,
                        val: observed_val,
                        ..
                    },
                ) => {
                    assert_eq!(ty, observed_ty);
                    assert_eq!(val, observed_val);
                }
                _ => panic!("both runs must produce the same definition kind"),
            }
            assert!(!capture.take().unwrap().is_empty());
        }
    }
}
