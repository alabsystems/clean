// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Untrusted ordinary-core advice search, following the adopted checker cursor.
//!
//! This does not use the diagnostic journal as a certificate. The returned bytes
//! are only a candidate; the actual checker must replay the original declaration.
//! Iota/K and the Init coverage surface remain unfinished. Extensional search
//! is bounded and proposes bytes for the adopted eta/irrelevance cursors. No trusted admission, validity theorem or completeness is claimed.
use super::{CoreTracer, Refusal, Token};
use crate::env::{Declaration, Environment};
use crate::expr::{stack_safe, Expr, ExprKind};
use crate::kcheck_trace::term::{Label, Node, Term};
use crate::kcheck_trace::wire::encode_tokens;
use crate::level::Level;

/// Candidate syntax and bytes, never an authority-bearing acceptance token.
#[derive(Debug)]
pub struct DeclarationAdvice {
    /// Proposed declaration-frame token sequence, starting with DEPTH.
    pub tokens: Vec<Token>,
    /// Native bytes to submit to the actual checker, without a frame prefix.
    pub bytes: Vec<u8>,
    /// Untrusted annotation, for retaining syntax only after actual acceptance.
    pub annotated_type: Term,
    /// Untrusted annotation of the proposed body.
    pub annotated_value: Term,
}

enum Step {
    Beta(Term, Term, Term, Label, Vec<(Term, Label)>),
    Zeta(Term, Term, Vec<(Term, Label)>),
    Local(Term, Vec<(Term, Label)>),
}

struct Producer<'a> {
    lookup: CoreTracer<'a>,
    context: Vec<(Term, Option<Term>)>,
    remaining: u64,
    tokens: Vec<Token>,
}

/// Produce candidate advice for an ordinary definition/theorem/opaque body.
/// `depth` is an untrusted proposal; insufficient depth is refused by the checker.
/// Search is separately bounded by `operations`. The environment supplies syntax,
/// not authority; every dependency and every proposed byte still needs replay.
pub fn produce_ordinary(
    env: &Environment,
    declaration: &Declaration,
    operations: u64,
    depth: u64,
) -> Result<DeclarationAdvice, Refusal> {
    let (ty, value) = match declaration {
        Declaration::Definition { type_, value, .. }
        | Declaration::Theorem { type_, value, .. }
        | Declaration::Opaque { type_, value, .. } => (type_, value),
        Declaration::Axiom { .. } => {
            return Err(Refusal::Coverage {
                source_name: "advice_axiom_declaration".into(),
                term: "axiom".into(),
            })
        }
    };
    let mut producer = Producer {
        lookup: CoreTracer::new(env, operations),
        context: Vec::new(),
        remaining: operations,
        tokens: vec![Token::Depth(depth)],
    };
    let (annotated_type, sort) = producer.check(ty)?;
    // Formation is needed here; the actual checker computes the report.
    let _declaration_universe = producer.require_sort(&sort)?;
    let (annotated_value, inferred) = producer.check(value)?;
    producer.conv(&inferred, &annotated_type)?;
    let bytes = encode_tokens(&producer.tokens);
    Ok(DeclarationAdvice {
        tokens: producer.tokens,
        bytes,
        annotated_type,
        annotated_value,
    })
}

impl Producer<'_> {
    fn tick(&mut self) -> Result<(), Refusal> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Refusal::Budget)?;
        Ok(())
    }
    fn missing(source: &str, term: &Term) -> Refusal {
        Refusal::Coverage {
            source_name: source.into(),
            term: term.erase().to_string().chars().take(512).collect(),
        }
    }
    fn check(&mut self, raw: &Expr) -> Result<(Term, Term), Refusal> {
        stack_safe(|| self.check_inner(raw))
    }
    fn check_inner(&mut self, raw: &Expr) -> Result<(Term, Term), Refusal> {
        self.tick()?;
        match raw.kind() {
            ExprKind::BVar(index) => {
                let index = usize::try_from(*index).map_err(|_| Refusal::Budget)?;
                let level = self
                    .context
                    .len()
                    .checked_sub(index)
                    .and_then(|rest| rest.checked_sub(1))
                    .ok_or_else(|| Refusal::Check("advice loose bound variable".into()))?;
                let ty = self.context[level].0.clone();
                Ok((
                    Term::new(Node::Local(
                        u32::try_from(level).map_err(|_| Refusal::Budget)?,
                    )),
                    ty,
                ))
            }
            ExprKind::Sort(level) => Ok((
                Term::new(Node::Sort(level.clone())),
                Term::new(Node::Sort(Level::succ(level.clone()))),
            )),
            ExprKind::Const(name, levels) => {
                let info = self
                    .lookup
                    .env
                    .get_const(name)
                    .ok_or_else(|| Refusal::Check(format!("advice unknown constant {name}")))?;
                let params = info.level_params.clone();
                if params.len() != levels.len() {
                    return Err(Refusal::Check("advice constant level arity".into()));
                }
                let ty = self
                    .lookup
                    .constant_type(name)?
                    .instantiate_levels(&params, levels);
                Ok((Term::new(Node::Const(name.clone(), levels.to_vec())), ty))
            }
            ExprKind::App(function, argument) => {
                let (function, function_type) = self.check(function)?;
                let function_type = self.whnf(&function_type)?;
                let Node::Pi(_, domain, body) = function_type.0.as_ref() else {
                    return Err(Refusal::Check("advice application type is not Pi".into()));
                };
                let (argument, inferred) = self.check(argument)?;
                self.conv(&inferred, domain)?;
                let result = body.instantiate(&argument);
                Ok((
                    Term::new(Node::App(
                        function,
                        argument,
                        Label::Checked(domain.clone()),
                    )),
                    result,
                ))
            }
            ExprKind::Lam(binder, domain, body) | ExprKind::Pi(binder, domain, body) => {
                let (domain, domain_type) = self.check(domain)?;
                let u = self.require_sort(&domain_type)?;
                let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push((domain.clone(), None));
                let result = (|| {
                    let (body, body_type) = self.check(body)?;
                    if matches!(raw.kind(), ExprKind::Lam(..)) {
                        Ok((
                            Term::new(Node::Lam(
                                *binder,
                                domain.clone(),
                                body.abstract_local(level),
                            )),
                            Term::new(Node::Pi(
                                *binder,
                                domain.clone(),
                                body_type.abstract_local(level),
                            )),
                        ))
                    } else {
                        // The checker still has the fresh context while normalizing TB.
                        let v = self.require_sort(&body_type)?;
                        Ok((
                            Term::new(Node::Pi(
                                *binder,
                                domain.clone(),
                                body.abstract_local(level),
                            )),
                            Term::new(Node::Sort(Level::imax(u, v))),
                        ))
                    }
                })();
                self.context.pop();
                result
            }
            ExprKind::Let(name, ty, value, body, _) => {
                let (ty, ty_type) = self.check(ty)?;
                let _let_universe = self.require_sort(&ty_type)?;
                let (value, value_type) = self.check(value)?;
                self.conv(&value_type, &ty)?;
                let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push((ty.clone(), Some(value.clone())));
                let result = self.check(body);
                self.context.pop();
                let (body, body_type) = result?;
                let body_type = body_type.abstract_local(level).instantiate(&value);
                Ok((
                    Term::new(Node::Let(
                        name.clone(),
                        ty,
                        value,
                        body.abstract_local(level),
                    )),
                    body_type,
                ))
            }
            ExprKind::MData(_, expression) => self.check(expression),
            _ => Err(Refusal::Coverage {
                source_name: "advice_non_core_input".into(),
                term: raw.to_string().chars().take(512).collect(),
            }),
        }
    }
    // This cursor is distinct from raw syntax checking: the adopted inferAnn
    // does not recheck a lambda domain or a let value, but an application
    // consumes its stored domain conversion and a Pi normalizes under its binder.
    fn infer_ann(&mut self, term: &Term) -> Result<Term, Refusal> {
        stack_safe(|| {
            self.tick()?;
            match term.0.as_ref() {
                Node::Local(level) => self
                    .context
                    .get(*level as usize)
                    .map(|entry| entry.0.clone())
                    .ok_or_else(|| Self::missing("advice_infer_unknown_local", term)),
                Node::Sort(level) => Ok(Term::new(Node::Sort(Level::succ(level.clone())))),
                Node::Const(name, levels) => {
                    let info = self
                        .lookup
                        .env
                        .get_const(name)
                        .ok_or_else(|| Self::missing("advice_infer_unknown_constant", term))?;
                    let params = info.level_params.clone();
                    Ok(self
                        .lookup
                        .constant_type(name)?
                        .instantiate_levels(&params, levels))
                }
                Node::App(function, argument, label) => {
                    let ty = self.infer_ann(function)?;
                    let ty = self.whnf(&ty)?;
                    let Node::Pi(_, domain, body) = ty.0.as_ref() else {
                        return Err(Self::missing("advice_infer_not_pi", term));
                    };
                    let Label::Checked(label) = label else {
                        return Err(Self::missing("advice_infer_missing_domain", term));
                    };
                    self.conv(label, domain)?;
                    Ok(body.instantiate(argument))
                }
                Node::Lam(binder, domain, body) => {
                    let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                    self.context.push((domain.clone(), None));
                    let result = self.infer_ann(&body.open(level));
                    self.context.pop();
                    Ok(Term::new(Node::Pi(
                        *binder,
                        domain.clone(),
                        result?.abstract_local(level),
                    )))
                }
                Node::Pi(_, domain, body) => {
                    let ty = self.infer_ann(domain)?;
                    let u = self.require_sort(&ty)?;
                    let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                    self.context.push((domain.clone(), None));
                    let result = (|| {
                        let ty = self.infer_ann(&body.open(level))?;
                        let v = self.require_sort(&ty)?;
                        Ok(Term::new(Node::Sort(Level::imax(u, v))))
                    })();
                    self.context.pop();
                    result
                }
                Node::Let(_, ty, value, body) => {
                    let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                    self.context.push((ty.clone(), Some(value.clone())));
                    let result = self.infer_ann(&body.open(level));
                    self.context.pop();
                    Ok(result?.abstract_local(level).instantiate(value))
                }
                _ => Err(Self::missing("advice_infer_non_core", term)),
            }
        })
    }
    fn eta(&mut self, function: &Term) -> Result<Term, Refusal> {
        let ty = self.infer_ann(function)?;
        let ty = self.whnf(&ty)?;
        let Node::Pi(binder, domain, _) = ty.0.as_ref() else {
            return Err(Self::missing("advice_eta_not_pi", function));
        };
        Ok(Term::new(Node::Lam(
            *binder,
            domain.clone(),
            Term::new(Node::App(
                function.clone(),
                Term::new(Node::BVar(0)),
                Label::Checked(domain.clone()),
            )),
        )))
    }
    fn require_sort(&mut self, ty: &Term) -> Result<Level, Refusal> {
        let reduced = self.whnf(ty)?;
        match reduced.0.as_ref() {
            Node::Sort(level) => Ok(level.clone()),
            _ => Err(Refusal::Check("advice expected sort".into())),
        }
    }
    fn spine(term: &Term) -> (Term, Vec<(Term, Label)>) {
        let mut head = term.clone();
        let mut arguments = Vec::new();
        while let Node::App(function, argument, label) = head.0.as_ref() {
            arguments.push((argument.clone(), label.clone()));
            head = function.clone();
        }
        arguments.reverse();
        (head, arguments)
    }
    fn apply(mut head: Term, arguments: Vec<(Term, Label)>) -> Term {
        for (argument, label) in arguments {
            head = Term::new(Node::App(head, argument, label));
        }
        head
    }
    fn redex(&self, term: &Term) -> Option<Step> {
        let (head, arguments) = Self::spine(term);
        match head.0.as_ref() {
            Node::Lam(_, domain, body) if !arguments.is_empty() => {
                let (argument, label) = arguments[0].clone();
                Some(Step::Beta(
                    domain.clone(),
                    body.clone(),
                    argument,
                    label,
                    arguments[1..].to_vec(),
                ))
            }
            Node::Let(_, _, value, body) => {
                Some(Step::Zeta(value.clone(), body.clone(), arguments))
            }
            Node::Local(level) => self
                .context
                .get(*level as usize)
                .and_then(|(_, value)| value.as_ref())
                .map(|value| Step::Local(value.clone(), arguments)),
            _ => None,
        }
    }
    fn step(&mut self, step: Step) -> Result<Term, Refusal> {
        self.tick()?;
        match step {
            Step::Beta(domain, body, argument, label, rest) => {
                let Label::Checked(label) = label else {
                    return Err(Self::missing("advice_beta_missing_domain", &body));
                };
                self.tokens.push(Token::Dom);
                self.conv(&label, &domain)?;
                Ok(Self::apply(body.instantiate(&argument), rest))
            }
            Step::Zeta(value, body, rest) => Ok(Self::apply(body.instantiate(&value), rest)),
            Step::Local(value, rest) => Ok(Self::apply(value, rest)),
        }
    }
    fn unfold(&mut self, term: &Term) -> Result<Option<Term>, Refusal> {
        let (head, arguments) = Self::spine(term);
        let Node::Const(name, levels) = head.0.as_ref() else {
            return Ok(None);
        };
        Ok(self
            .lookup
            .constant_value(name, levels)?
            .map(|body| Self::apply(body, arguments)))
    }
    fn whnf(&mut self, term: &Term) -> Result<Term, Refusal> {
        stack_safe(|| {
            self.tick()?;
            if let Some(step) = self.redex(term) {
                self.tokens.push(Token::CoreL(1));
                let next = self.step(step)?;
                self.whnf(&next)
            } else if let Some(next) = self.unfold(term)? {
                self.tokens.push(Token::DeltaL);
                self.whnf(&next)
            } else {
                self.tokens.push(Token::Stop);
                Ok(term.clone())
            }
        })
    }
    fn attempt(
        &mut self,
        branch: impl FnOnce(&mut Self) -> Result<(), Refusal>,
    ) -> Result<bool, Refusal> {
        let mark = self.tokens.len();
        let result = branch(self);
        match result {
            Ok(()) => Ok(true),
            Err(error) => {
                self.tokens.truncate(mark);
                if matches!(error, Refusal::Budget) {
                    Err(error)
                } else {
                    Ok(false)
                }
            }
        }
    }
    fn structural(&mut self, left: &Term, right: &Term) -> Result<(), Refusal> {
        match (left.0.as_ref(), right.0.as_ref()) {
            (Node::Sort(u), Node::Sort(v)) if self.lookup.levels_equal(u, v) => {
                self.tokens.push(Token::Sort);
                Ok(())
            }
            (Node::Const(c, us), Node::Const(d, vs))
                if c == d
                    && us.len() == vs.len()
                    && us
                        .iter()
                        .zip(vs)
                        .all(|(u, v)| self.lookup.levels_equal(u, v)) =>
            {
                self.tokens.push(Token::Const);
                Ok(())
            }
            (Node::App(f, a, _), Node::App(g, b, _)) => {
                self.tokens.push(Token::App);
                self.conv(f, g)?;
                self.conv(a, b)
            }
            (Node::Lam(_, a, b), Node::Lam(_, c, d)) | (Node::Pi(_, a, b), Node::Pi(_, c, d)) => {
                self.tokens
                    .push(if matches!(left.0.as_ref(), Node::Lam(..)) {
                        Token::Lam
                    } else {
                        Token::Pi
                    });
                self.conv(a, c)?;
                let level = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push((a.clone(), None));
                let result = self.conv(&b.open(level), &d.open(level));
                self.context.pop();
                result
            }
            _ => Err(Self::missing("advice_structural_conversion", left)),
        }
    }
    fn conv(&mut self, left: &Term, right: &Term) -> Result<(), Refusal> {
        stack_safe(|| {
            self.tick()?;
            // Rust's Level constructors normalize, whereas the adopted
            // checker retains e.g. imax 0 0 in an inferred sort. Native
            // erasure equality therefore cannot justify its syntactic REFL
            // for a composite term. Compare levels with SORT/CONST and walk
            // composite structure; only variable indices have no lost level
            // syntax. The actual checker still decides every emitted token.
            if matches!((left.0.as_ref(), right.0.as_ref()),
                (Node::Local(a), Node::Local(b)) | (Node::BVar(a), Node::BVar(b)) if a == b)
            {
                self.tokens.push(Token::Refl);
                return Ok(());
            }
            if self.attempt(|this| this.structural(left, right))? {
                return Ok(());
            }
            if self.attempt(|this| {
                let step = this
                    .redex(left)
                    .ok_or_else(|| Self::missing("advice_no_left_step", left))?;
                this.tokens.push(Token::CoreL(1));
                let next = this.step(step)?;
                // conv already supplied the first pending step to whnf.
                let normal = this.whnf(&next)?;
                this.conv(&normal, right)
            })? {
                return Ok(());
            }
            if self.attempt(|this| {
                let step = this
                    .redex(right)
                    .ok_or_else(|| Self::missing("advice_no_right_step", right))?;
                this.tokens.push(Token::CoreR(1));
                let next = this.step(step)?;
                let normal = this.whnf(&next)?;
                this.conv(left, &normal)
            })? {
                return Ok(());
            }
            if self.attempt(|this| {
                let next = this
                    .unfold(left)?
                    .ok_or_else(|| Self::missing("advice_no_left_delta", left))?;
                this.tokens.push(Token::DeltaL);
                this.conv(&next, right)
            })? {
                return Ok(());
            }
            if self.attempt(|this| {
                let next = this
                    .unfold(right)?
                    .ok_or_else(|| Self::missing("advice_no_right_delta", right))?;
                this.tokens.push(Token::DeltaR);
                this.conv(left, &next)
            })? {
                return Ok(());
            }
            if !matches!(left.0.as_ref(), Node::Lam(..))
                && matches!(right.0.as_ref(), Node::Lam(..))
                && self.attempt(|this| {
                    this.tokens.push(Token::EtaL);
                    let expanded = this.eta(left)?;
                    this.conv(&expanded, right)
                })?
            {
                return Ok(());
            }
            if matches!(left.0.as_ref(), Node::Lam(..))
                && !matches!(right.0.as_ref(), Node::Lam(..))
                && self.attempt(|this| {
                    this.tokens.push(Token::EtaR);
                    let expanded = this.eta(right)?;
                    this.conv(left, &expanded)
                })?
            {
                return Ok(());
            }
            if self.attempt(|this| {
                this.tokens.push(Token::Irrel);
                let left_type = this.infer_ann(left)?;
                let right_type = this.infer_ann(right)?;
                let universe = this.infer_ann(&left_type)?;
                let universe = this.require_sort(&universe)?;
                if !this.lookup.levels_equal(&universe, &Level::zero()) {
                    return Err(Self::missing("advice_irrel_not_prop", left));
                }
                this.conv(&left_type, &right_type)
            })? {
                return Ok(());
            }
            Err(Self::missing("advice_conversion_search_incomplete", left))
        })
    }
}
