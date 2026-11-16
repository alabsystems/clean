// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source dictionary elimination for translation validation. Class names and
//! instance names confer no arithmetic meaning: only the stored field does.
//! This is separate from compiler lowering. Named definitions are unfolded only
//! in the original source environment, and all reduction is bounded core
//! delta/beta/zeta/metadata elimination. Unknown or opaque dictionaries refuse.

use super::{is_const_named, source_head_name, Expr, ExprKind, ReflectError};
use clean_kernel::Environment;
use std::cell::Cell;

pub(super) struct SourceInstances<'a> {
    environment: Option<&'a Environment>,
    remaining: Cell<usize>,
}

impl<'a> SourceInstances<'a> {
    pub(super) fn new(environment: Option<&'a Environment>) -> Self {
        Self {
            environment,
            remaining: Cell::new(1024),
        }
    }

    fn step(&self) -> Result<(), ReflectError> {
        let left = self.remaining.get().checked_sub(1).ok_or_else(|| {
            ReflectError::unsupported(
                "source instance reduction budget exhausted (fail-closed)".to_string(),
            )
        })?;
        self.remaining.set(left);
        Ok(())
    }

    /// Reduce just the application head. A constructor is a stopping point;
    /// primitive arithmetic heads are never unfolded by `apply`.
    fn head(&self, expression: &Expr, constructor: Option<&str>) -> Result<Expr, ReflectError> {
        let mut current = expression.clone();
        loop {
            let next = {
                let head = current.get_app_fn();
                let args = current.get_app_args();
                if let ExprKind::Const(name, _) = head.kind() {
                    source_head_name(name)?;
                }
                match head.kind() {
                    ExprKind::MData(_, inner) => Some(Expr::apps(
                        (**inner).clone(),
                        args.iter().map(|a| (*a).clone()),
                    )),
                    ExprKind::Let(_, _, value, body, _) => Some(Expr::apps(
                        body.instantiate(value),
                        args.iter().map(|a| (*a).clone()),
                    )),
                    ExprKind::Lam(_, _, body) if !args.is_empty() => Some(Expr::apps(
                        body.instantiate(args[0]),
                        args[1..].iter().map(|a| (*a).clone()),
                    )),
                    ExprKind::Const(name, levels)
                        if constructor.is_some_and(|ctor| !is_const_named(head, ctor)) =>
                    {
                        self.environment
                            .and_then(|env| env.unfold(name, levels))
                            .map(|value| Expr::apps(value, args.iter().map(|a| (*a).clone())))
                    }
                    ExprKind::BVar(_)
                    | ExprKind::FVar(_)
                    | ExprKind::Sort(_)
                    | ExprKind::Const(..)
                    | ExprKind::App(..)
                    | ExprKind::Lam(..)
                    | ExprKind::Pi(..)
                    | ExprKind::Lit(_)
                    | ExprKind::Proj(..)
                    | ExprKind::SProp
                    | ExprKind::Squash(_)
                    | ExprKind::CubicalInterval
                    | ExprKind::CubicalI0
                    | ExprKind::CubicalI1
                    | ExprKind::CubicalPath { .. }
                    | ExprKind::CubicalPathLam { .. }
                    | ExprKind::CubicalPathApp { .. }
                    | ExprKind::CubicalHComp { .. }
                    | ExprKind::CubicalTransp { .. }
                    | ExprKind::CubicalCoe { .. }
                    | ExprKind::ZFCSet(_)
                    | ExprKind::ZFCMem { .. }
                    | ExprKind::ZFCComprehension { .. } => None,
                }
            };
            let Some(next) = next else { return Ok(current) };
            self.step()?;
            current = next;
        }
    }

    pub(super) fn field(
        &self,
        dictionary: &Expr,
        constructor: &str,
        parameters: &[&Expr],
    ) -> Result<Expr, ReflectError> {
        self.step()?;
        let reduced = self.head(dictionary, Some(constructor))?;
        let args = reduced.get_app_args();
        if !is_const_named(reduced.get_app_fn(), constructor)
            || args.len() != parameters.len() + 1
            || args[..parameters.len()] != *parameters
        {
            return Err(ReflectError::unsupported(format!(
                "source instance dictionary did not resolve to `{constructor}` with the requested parameters (fail-closed)"
            )));
        }
        Ok(args[parameters.len()].clone())
    }

    pub(super) fn apply(&self, function: Expr, args: &[&Expr]) -> Result<Expr, ReflectError> {
        self.head(
            &Expr::apps(function, args.iter().map(|a| (*a).clone())),
            None,
        )
    }
}
