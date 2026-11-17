// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Untrusted ordinary-core advice search, following the adopted checker cursor.
//!
//! This does not use the diagnostic journal as a certificate. The returned bytes
//! are only a candidate; the actual checker must replay the original declaration.
//! Iota/K search is restricted to value-less `MajorAfterMinors` recursors whose
//! admitted labelled syntax is available. The wider Init coverage surface
//! remains unfinished. Extensional search is bounded and proposes bytes for the
//! adopted eta/irrelevance cursors. No trusted admission, validity theorem or
//! completeness is claimed.
use super::{CoreTracer, LabelledEnvironment, Refusal, Token};
use crate::env::{Declaration, Environment};
use crate::expr::{stack_safe, Expr, ExprKind};
use crate::inductive::{RecursorArgOrder, RecursorVal};
use crate::kcheck_trace::term::{Label, Node, Term};
use crate::kcheck_trace::wire::encode_tokens;
use crate::level::Level;
use crate::name::Name;

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
    Recursor(RecursorVal, Vec<Level>, Vec<(Term, Label)>),
}

struct Producer<'a> {
    lookup: CoreTracer<'a>,
    context: Vec<(Term, Option<Term>)>,
    remaining: u64,
    tokens: Vec<Token>,
}

/// Produce candidate advice for an ordinary definition/theorem/opaque body.
/// `depth` is an untrusted proposal; insufficient depth is refused by the checker.
/// Search heartbeats are separately bounded by `operations`; this is not a
/// CPU-step cap because persistent terms are cloned and transformed without a
/// heartbeat for every shared DAG node. The environment supplies syntax, not
/// authority; every dependency and every proposed byte still needs replay.
pub fn produce_ordinary(
    env: &Environment,
    declaration: &Declaration,
    operations: u64,
    depth: u64,
) -> Result<DeclarationAdvice, Refusal> {
    produce_ordinary_with_lookup(
        CoreTracer::new(env, operations),
        declaration,
        operations,
        depth,
    )
}

/// Produce candidate advice while reusing the persistent labelled syntax of
/// the already admitted prefix. This is the only entry that enables the
/// bounded recursor search; the compatibility entry above retains its former
/// ordinary-core surface. The labelled table is syntax, never authority.
pub fn produce_ordinary_with_labelled(
    env: &Environment,
    labelled: &LabelledEnvironment,
    declaration: &Declaration,
    operations: u64,
    depth: u64,
) -> Result<DeclarationAdvice, Refusal> {
    produce_ordinary_with_lookup(
        CoreTracer::with_labelled_environment(env, labelled, operations),
        declaration,
        operations,
        depth,
    )
}

fn produce_ordinary_with_lookup(
    lookup: CoreTracer<'_>,
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
        lookup,
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
    fn unsupported_recursor(source: &str, name: &Name) -> Refusal {
        Refusal::Coverage {
            source_name: source.into(),
            term: name.to_unambiguous_string(),
        }
    }
    fn recursor_counts(rec: &RecursorVal) -> Result<(usize, usize), Refusal> {
        let leading =
            u64::from(rec.num_params) + u64::from(rec.num_motives) + u64::from(rec.num_minors);
        let arity = leading + u64::from(rec.num_indices) + 1;
        Ok((
            usize::try_from(leading).map_err(|_| Refusal::Budget)?,
            usize::try_from(arity).map_err(|_| Refusal::Budget)?,
        ))
    }
    fn labelled_type(&self, name: &Name, source: &str) -> Result<Term, Refusal> {
        self.lookup
            .labelled
            .and_then(|labelled| labelled.entries.get(name))
            .map(|(ty, _)| ty.clone())
            .ok_or_else(|| Self::unsupported_recursor(source, name))
    }
    fn labelled_rule(&self, recursor: &Name, constructor: &Name) -> Result<Term, Refusal> {
        self.lookup
            .labelled
            .and_then(|labelled| labelled.rules.get(&(recursor.clone(), constructor.clone())))
            .cloned()
            .ok_or_else(|| Self::unsupported_recursor("advice_recursor_labelled_rule", recursor))
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
    /// Emit exactly one adopted `walk` mode token, followed by one conversion
    /// per argument only in certificate mode. Even an empty constructor spine
    /// consumes its mode token.
    fn walk_spine(&mut self, mut ty: Term, arguments: &[(Term, Label)]) -> Result<Term, Refusal> {
        let mark = self.tokens.len();
        let result = (|| {
            self.tick()?;
            let mut domains = Vec::new();
            let mut all_reflexive = true;
            for (argument, label) in arguments {
                self.tick()?;
                let Node::Pi(_, domain, body) = ty.0.as_ref() else {
                    return Err(Self::missing("advice_recursor_telescope_short", &ty));
                };
                let domain = domain.clone();
                let body = body.clone();
                all_reflexive &=
                    matches!(label, Label::Checked(stored) if stored.erased_eq(&domain));
                domains.push(domain);
                ty = body.instantiate(argument);
            }
            let arity = u64::try_from(arguments.len()).map_err(|_| Refusal::Budget)?;
            if all_reflexive {
                self.tokens.push(Token::SpineRefl(arity));
            } else {
                self.tokens.push(Token::SpineCerts(arity));
                for ((argument, label), domain) in arguments.iter().zip(&domains) {
                    let Label::Checked(stored) = label else {
                        return Err(Self::missing(
                            "advice_recursor_missing_spine_label",
                            argument,
                        ));
                    };
                    self.conv(stored, domain)?;
                }
            }
            Ok(ty)
        })();
        if result.is_err() {
            self.tokens.truncate(mark);
        }
        result
    }
    /// Read the constructor's stored result before substituting its binders,
    /// exactly as `ctorStoredResult`/`ctorResultArgs` do. Substituting the whole
    /// result first would be wrong when a bound head contributes a new spine.
    fn stored_result_arguments(
        &mut self,
        constructor_type: &Term,
        level_params: &[Name],
        levels: &[Level],
        binder_arguments: &[(Term, Label)],
        family: &Name,
        expected: usize,
    ) -> Result<Vec<Term>, Refusal> {
        self.tick()?;
        let mut stored_result = constructor_type.clone();
        for _ in binder_arguments {
            self.tick()?;
            let Node::Pi(_, _, body) = stored_result.0.as_ref() else {
                return Err(Self::missing(
                    "advice_recursor_telescope_short",
                    &stored_result,
                ));
            };
            stored_result = body.clone();
        }
        let (head, arguments) = Self::spine(&stored_result);
        let Node::Const(actual_family, _) = head.0.as_ref() else {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_result",
                family,
            ));
        };
        if actual_family != family || arguments.len() != expected {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_result",
                family,
            ));
        }
        let instantiated_head = head.instantiate_levels(level_params, levels);
        let Node::Const(_, actual_levels) = instantiated_head.0.as_ref() else {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_result",
                family,
            ));
        };
        if actual_levels.len() != levels.len()
            || !actual_levels
                .iter()
                .zip(levels)
                .all(|(left, right)| self.lookup.levels_equal(left, right))
        {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_levels",
                family,
            ));
        }
        let mut result = Vec::new();
        for (argument, _) in arguments {
            self.tick()?;
            let mut argument = argument.instantiate_levels(level_params, levels);
            for (binder, _) in binder_arguments.iter().rev() {
                self.tick()?;
                argument = argument.instantiate(binder);
            }
            result.push(argument);
        }
        Ok(result)
    }
    /// `REFL` is valid for an exact erased tie even though general conversion
    /// search expands composite terms to preserve level provenance.
    fn tie_conv(&mut self, left: &Term, right: &Term) -> Result<(), Refusal> {
        self.tick()?;
        if left.erased_eq(right) {
            self.tokens.push(Token::Refl);
            Ok(())
        } else {
            self.conv(left, right)
        }
    }
    fn recursor_iota(
        &mut self,
        rec: &RecursorVal,
        levels: &[Level],
        arguments: &[(Term, Label)],
        recursor_type: &Term,
    ) -> Result<Term, Refusal> {
        self.tokens.push(Token::Iota);
        let (leading, arity) = Self::recursor_counts(rec)?;
        let major_index = arity.checked_sub(1).ok_or(Refusal::Budget)?;
        let major = arguments
            .get(major_index)
            .map(|(term, _)| term.clone())
            .ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_missing_major", &rec.name)
            })?;

        // IOTA precedes this complete nested WHNF script, including STOP.
        let major = self.whnf(&major)?;
        let (constructor, constructor_arguments) = Self::spine(&major);
        let (constructor_name, constructor_levels) = match constructor.0.as_ref() {
            Node::Const(name, levels) => (name.clone(), levels.clone()),
            _ => {
                return Err(Self::unsupported_recursor(
                    "advice_recursor_major_not_constructor",
                    &rec.name,
                ))
            }
        };
        let rule = rec
            .rules
            .iter()
            .find(|rule| rule.constructor_name == constructor_name)
            .cloned()
            .ok_or_else(|| {
                Self::unsupported_recursor(
                    "advice_recursor_constructor_outside_family",
                    &constructor_name,
                )
            })?;
        let constructor_info = self
            .lookup
            .env
            .get_constructor(&constructor_name)
            .cloned()
            .ok_or_else(|| {
                Self::unsupported_recursor(
                    "advice_recursor_constructor_metadata",
                    &constructor_name,
                )
            })?;
        let constructor_entry = self
            .lookup
            .env
            .get_const(&constructor_name)
            .cloned()
            .ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_constructor_entry", &constructor_name)
            })?;
        if constructor_info.inductive_name != rec.inductive_name
            || constructor_info.num_params != rec.num_params
            || constructor_info.num_fields != rule.num_fields
            || constructor_info.level_params != constructor_entry.level_params
        {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_shape",
                &constructor_name,
            ));
        }
        let constructor_arity =
            usize::try_from(u64::from(rec.num_params) + u64::from(rule.num_fields))
                .map_err(|_| Refusal::Budget)?;
        if constructor_arguments.len() != constructor_arity {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_arity",
                &constructor_name,
            ));
        }
        let eliminated_levels = rec
            .level_params
            .len()
            .checked_sub(constructor_entry.level_params.len())
            .ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_constructor_levels", &constructor_name)
            })?;
        if rec.level_params[eliminated_levels..] != constructor_entry.level_params {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_levels",
                &constructor_name,
            ));
        }
        let expected_constructor_levels = &levels[eliminated_levels..];
        if constructor_levels.len() != expected_constructor_levels.len()
            || !constructor_levels
                .iter()
                .zip(expected_constructor_levels)
                .all(|(left, right)| self.lookup.levels_equal(left, right))
        {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_levels",
                &constructor_name,
            ));
        }

        let recursor_type = recursor_type.instantiate_levels(&rec.level_params, levels);
        self.walk_spine(recursor_type, &arguments[..arity])?;
        let constructor_type = self.labelled_type(
            &constructor_name,
            "advice_recursor_labelled_constructor_type",
        )?;
        self.walk_spine(
            constructor_type
                .instantiate_levels(&constructor_entry.level_params, &constructor_levels),
            &constructor_arguments,
        )?;

        let params = usize::try_from(rec.num_params).map_err(|_| Refusal::Budget)?;
        let indices = usize::try_from(rec.num_indices).map_err(|_| Refusal::Budget)?;
        let result_arity = params.checked_add(indices).ok_or(Refusal::Budget)?;
        let result_arguments = self.stored_result_arguments(
            &constructor_type,
            &constructor_entry.level_params,
            &constructor_levels,
            &constructor_arguments,
            &rec.inductive_name,
            result_arity,
        )?;
        let mut recursor_result_arguments = arguments
            .iter()
            .take(params)
            .map(|(term, _)| term.clone())
            .collect::<Vec<_>>();
        recursor_result_arguments.extend(
            arguments
                .iter()
                .skip(leading)
                .take(indices)
                .map(|(term, _)| term.clone()),
        );
        if recursor_result_arguments.len() != result_arity {
            return Err(Self::unsupported_recursor(
                "advice_recursor_result_arity",
                &rec.name,
            ));
        }
        for (constructor_argument, recursor_argument) in
            result_arguments.iter().zip(&recursor_result_arguments)
        {
            // IOTA's adopted direction is stored constructor result, then recursor.
            self.tie_conv(constructor_argument, recursor_argument)?;
        }

        let rhs = self
            .labelled_rule(&rec.name, &constructor_name)?
            .instantiate_levels(&rec.level_params, levels);
        if !matches!(rhs.0.as_ref(), Node::Lam(..)) {
            return Err(Self::unsupported_recursor(
                "advice_recursor_rule_shape",
                &rec.name,
            ));
        }
        let mut supplied = arguments.iter().take(leading).cloned().collect::<Vec<_>>();
        supplied.extend(constructor_arguments.iter().skip(params).cloned());
        supplied.extend(arguments.iter().skip(arity).cloned());
        Ok(Self::apply(rhs, supplied))
    }
    fn recursor_k(
        &mut self,
        rec: &RecursorVal,
        levels: &[Level],
        arguments: &[(Term, Label)],
        recursor_type: &Term,
    ) -> Result<Term, Refusal> {
        self.tokens.push(Token::K);
        if !rec.is_k || rec.rules.len() != 1 || rec.num_minors != 1 {
            return Err(Self::unsupported_recursor(
                "advice_recursor_k_shape",
                &rec.name,
            ));
        }
        let rule = rec.rules[0].clone();
        if rule.num_fields != 0 {
            return Err(Self::unsupported_recursor(
                "advice_recursor_k_shape",
                &rec.name,
            ));
        }
        let constructor_name = rule.constructor_name;
        let constructor_info = self
            .lookup
            .env
            .get_constructor(&constructor_name)
            .cloned()
            .ok_or_else(|| {
                Self::unsupported_recursor(
                    "advice_recursor_constructor_metadata",
                    &constructor_name,
                )
            })?;
        let constructor_entry = self
            .lookup
            .env
            .get_const(&constructor_name)
            .cloned()
            .ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_constructor_entry", &constructor_name)
            })?;
        if constructor_info.inductive_name != rec.inductive_name
            || constructor_info.num_params != rec.num_params
            || constructor_info.num_fields != 0
            || constructor_info.level_params != constructor_entry.level_params
        {
            return Err(Self::unsupported_recursor(
                "advice_recursor_k_shape",
                &rec.name,
            ));
        }
        let eliminated_levels = rec
            .level_params
            .len()
            .checked_sub(constructor_entry.level_params.len())
            .ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_constructor_levels", &constructor_name)
            })?;
        if rec.level_params[eliminated_levels..] != constructor_entry.level_params {
            return Err(Self::unsupported_recursor(
                "advice_recursor_constructor_levels",
                &constructor_name,
            ));
        }
        let constructor_levels = &levels[eliminated_levels..];
        let (leading, arity) = Self::recursor_counts(rec)?;
        let recursor_type = recursor_type.instantiate_levels(&rec.level_params, levels);
        self.walk_spine(recursor_type, &arguments[..arity])?;

        // K reads fixed indices from stored constructor syntax without a
        // constructor walk token.
        let params = usize::try_from(rec.num_params).map_err(|_| Refusal::Budget)?;
        let indices = usize::try_from(rec.num_indices).map_err(|_| Refusal::Budget)?;
        let result_arity = params.checked_add(indices).ok_or(Refusal::Budget)?;
        let constructor_type = self.labelled_type(
            &constructor_name,
            "advice_recursor_labelled_constructor_type",
        )?;
        let result_arguments = self.stored_result_arguments(
            &constructor_type,
            &constructor_entry.level_params,
            constructor_levels,
            &arguments[..params],
            &rec.inductive_name,
            result_arity,
        )?;
        let constructor_indices = result_arguments.iter().skip(params).take(indices);
        let recursor_indices = arguments.iter().skip(leading).take(indices);
        if constructor_indices.clone().count() != indices
            || recursor_indices.clone().count() != indices
        {
            return Err(Self::unsupported_recursor(
                "advice_recursor_k_shape",
                &rec.name,
            ));
        }
        for (constructor_index, (recursor_index, _)) in constructor_indices.zip(recursor_indices) {
            // K's adopted direction is recursor index, then fixed index.
            self.tie_conv(recursor_index, constructor_index)?;
        }

        let minor_index = usize::try_from(u64::from(rec.num_params) + u64::from(rec.num_motives))
            .map_err(|_| Refusal::Budget)?;
        let (minor, _) = arguments
            .get(minor_index)
            .cloned()
            .ok_or_else(|| Self::unsupported_recursor("advice_recursor_k_shape", &rec.name))?;
        Ok(Self::apply(
            minor,
            arguments.iter().skip(arity).cloned().collect(),
        ))
    }
    fn recursor_step(
        &mut self,
        rec: RecursorVal,
        levels: Vec<Level>,
        arguments: Vec<(Term, Label)>,
    ) -> Result<Term, Refusal> {
        let mark = self.tokens.len();
        let result = (|| {
            if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
                return Err(Self::unsupported_recursor(
                    "advice_recursor_argument_order",
                    &rec.name,
                ));
            }
            let entry =
                self.lookup.env.get_const(&rec.name).ok_or_else(|| {
                    Self::unsupported_recursor("advice_recursor_entry", &rec.name)
                })?;
            let metadata_arity = u64::from(rec.num_params)
                + u64::from(rec.num_motives)
                + u64::from(rec.num_minors)
                + u64::from(rec.num_indices)
                + 1;
            if entry.value.is_some()
                || entry.level_params != rec.level_params
                // `validate_metadata` uses u32 arithmetic internally. Guard it
                // so hostile metadata refuses rather than overflowing first.
                || metadata_arity > u64::from(u32::MAX)
                || rec.validate_metadata().is_err()
            {
                return Err(Self::unsupported_recursor(
                    "advice_recursor_metadata",
                    &rec.name,
                ));
            }
            let (_, arity) = Self::recursor_counts(&rec)?;
            if arguments.len() < arity || levels.len() != rec.level_params.len() {
                return Err(Self::unsupported_recursor(
                    "advice_recursor_arity",
                    &rec.name,
                ));
            }
            let recursor_type = self.labelled_type(&rec.name, "advice_recursor_labelled_type")?;
            let major_index = arity.checked_sub(1).ok_or(Refusal::Budget)?;
            let major = arguments.get(major_index).ok_or_else(|| {
                Self::unsupported_recursor("advice_recursor_missing_major", &rec.name)
            })?;
            let (major_head, _) = Self::spine(&major.0);
            let raw_constructor = matches!(
                major_head.0.as_ref(),
                Node::Const(name, _) if self.lookup.env.get_constructor(name).is_some()
            );
            if rec.is_k && !raw_constructor {
                self.recursor_k(&rec, &levels, &arguments, &recursor_type)
            } else {
                self.recursor_iota(&rec, &levels, &arguments, &recursor_type)
            }
        })();
        if result.is_err() {
            self.tokens.truncate(mark);
        }
        result
    }
    fn redex(&self, term: &Term) -> Result<Option<Step>, Refusal> {
        let (head, arguments) = Self::spine(term);
        let step = match head.0.as_ref() {
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
            Node::Const(name, levels) if self.lookup.labelled.is_some() => {
                let Some(rec) = self.lookup.env.get_recursor(name).cloned() else {
                    return Ok(None);
                };
                let (_, arity) = Self::recursor_counts(&rec)?;
                if arguments.len() < arity {
                    return Ok(None);
                }
                let entry = self
                    .lookup
                    .env
                    .get_const(name)
                    .ok_or_else(|| Self::unsupported_recursor("advice_recursor_entry", name))?;
                if entry.value.is_some() {
                    // A recursor-shaped definition is still an ordinary delta
                    // redex. Preserve the pre-IOTA/K producer path by letting
                    // `whnf` fall through to `unfold` instead of turning the
                    // bounded value-less restriction into a coverage loss.
                    return Ok(None);
                }
                Some(Step::Recursor(rec, levels.clone(), arguments))
            }
            _ => None,
        };
        Ok(step)
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
            Step::Recursor(rec, levels, arguments) => self.recursor_step(rec, levels, arguments),
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
            if let Some(step) = self.redex(term)? {
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
                    .redex(left)?
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
                    .redex(right)?
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinderData;

    #[test]
    fn unsupported_major_after_motive_recursor_rolls_back_without_tokens() {
        let mut env = Environment::default();
        env.init_nat().expect("native Nat fixture");
        let mut rec = env
            .get_recursor(&Name::from_string("Nat.rec"))
            .expect("Nat.rec metadata")
            .clone();
        rec.arg_order = RecursorArgOrder::MajorAfterMotive;
        let mut producer = Producer {
            lookup: CoreTracer::new(&env, 100),
            context: Vec::new(),
            remaining: 100,
            tokens: vec![Token::Depth(32)],
        };
        let before = producer.tokens.clone();
        assert!(matches!(
            producer.recursor_step(rec, Vec::new(), Vec::new()),
            Err(Refusal::Coverage { source_name, .. })
                if source_name == "advice_recursor_argument_order"
        ));
        assert_eq!(producer.tokens, before, "refusal exported no partial frame");
    }

    #[test]
    fn late_missing_recursor_rule_rolls_back_without_tokens() {
        let mut env = Environment::default();
        env.init_nat().expect("native Nat fixture");
        let nat = Name::from_string("Nat");
        let zero = Name::from_string("Nat.zero");
        let recursor = Name::from_string("Nat.rec");
        let names = [
            nat.clone(),
            zero.clone(),
            Name::from_string("Nat.succ"),
            recursor.clone(),
        ];
        let mut prefix_tracer = CoreTracer::new(&env, 1_000_000);
        let mut labelled = prefix_tracer
            .annotate_group(&names)
            .expect("labelled native Nat prefix");

        let nat_term = Expr::const_(nat, vec![]);
        let zero_term = Expr::const_(zero.clone(), vec![]);
        let motive = Expr::lam(BinderData::default(), nat_term.clone(), nat_term.clone());
        let successor_minor = Expr::lam(
            BinderData::default(),
            nat_term.clone(),
            Expr::lam(BinderData::default(), nat_term.clone(), zero_term.clone()),
        );
        let raw = Expr::apps(
            Expr::const_(recursor.clone(), vec![Level::succ(Level::zero())]),
            [motive, zero_term.clone(), successor_minor, zero_term],
        );
        let annotated = {
            let mut tracer = CoreTracer::with_labelled_environment(&env, &labelled, 1_000_000);
            tracer.check(&raw).expect("annotated Nat.zero recursor").0
        };
        let (head, arguments) = Producer::spine(&annotated);
        let Node::Const(name, levels) = head.0.as_ref() else {
            panic!("annotated recursor application retains its constant head");
        };
        assert_eq!(name, &recursor);
        assert!(
            labelled.rules.remove(&(recursor.clone(), zero)).is_some(),
            "fixture removes the late rule and no other syntax"
        );
        let rec = env
            .get_recursor(&recursor)
            .expect("Nat.rec metadata")
            .clone();
        let mut producer = Producer {
            lookup: CoreTracer::with_labelled_environment(&env, &labelled, 1_000_000),
            context: Vec::new(),
            remaining: 1_000_000,
            tokens: vec![Token::Depth(32)],
        };
        let before = producer.tokens.clone();
        assert!(matches!(
            producer.recursor_step(rec, levels.clone(), arguments),
            Err(Refusal::Coverage { source_name, .. })
                if source_name == "advice_recursor_labelled_rule"
        ));
        assert_eq!(
            producer.tokens, before,
            "late missing-rule refusal exported no partial frame"
        );
    }
}
