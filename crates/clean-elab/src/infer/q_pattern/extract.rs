// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern variable extraction from q-pattern surface expressions.

use super::super::ElabCtx;
use crate::stack_safe;
use clean_kernel::Expr;
use clean_parser::{QAntiquotContent, SurfaceExpr};
use std::collections::HashSet;

/// Result of matching a q-pattern against a scrutinee
pub struct QPatternMatchResult {
    /// Pattern variable bindings: name -> (value, type)
    pub bindings: Vec<(String, Expr, Expr)>,
}

impl<'a> ElabCtx<'a> {
    /// Extract pattern variables from a q-pattern expression
    ///
    /// Walks the surface expression looking for $-antiquotations that bind
    /// pattern variables. Returns a list of (name, optional_type_annotation).
    pub(in crate::infer) fn extract_q_pattern_vars(
        &self,
        expr: &SurfaceExpr,
    ) -> Vec<(String, Option<SurfaceExpr>)> {
        let mut vars = Vec::new();
        let mut seen = HashSet::new();
        self.collect_q_pattern_vars(expr, &mut vars, &mut seen);
        vars
    }

    /// Recursively collect pattern variables from a q-pattern
    fn collect_q_pattern_vars(
        &self,
        expr: &SurfaceExpr,
        vars: &mut Vec<(String, Option<SurfaceExpr>)>,
        seen: &mut HashSet<String>,
    ) {
        stack_safe(|| match expr {
            SurfaceExpr::QAntiquot { content, .. } => {
                match content {
                    QAntiquotContent::Simple(name) => {
                        // $x - simple pattern variable
                        if seen.insert(name.clone()) {
                            vars.push((name.clone(), None));
                        }
                    }
                    QAntiquotContent::Typed { name, ty } => {
                        // $(x : τ) - typed pattern variable
                        if seen.insert(name.clone()) {
                            vars.push((name.clone(), Some((**ty).clone())));
                        }
                    }
                    QAntiquotContent::Expr(_) => {
                        // $(expr) in pattern position - expression to match, not a binding
                    }
                    QAntiquotContent::Splice { name, .. } => {
                        // $[xs]* - splice pattern variable (list)
                        if seen.insert(name.clone()) {
                            vars.push((name.clone(), None));
                        }
                    }
                }
            }

            SurfaceExpr::App(_, func, args) => {
                self.collect_q_pattern_vars(func, vars, seen);
                for arg in args {
                    self.collect_q_pattern_vars(&arg.expr, vars, seen);
                }
            }

            SurfaceExpr::Paren(_, inner) => {
                self.collect_q_pattern_vars(inner, vars, seen);
            }

            SurfaceExpr::Lambda(_, _, body) => {
                self.collect_q_pattern_vars(body, vars, seen);
            }

            SurfaceExpr::Pi(_, _, body) => {
                self.collect_q_pattern_vars(body, vars, seen);
            }

            SurfaceExpr::Arrow(_, from, to) => {
                self.collect_q_pattern_vars(from, vars, seen);
                self.collect_q_pattern_vars(to, vars, seen);
            }

            SurfaceExpr::Let(_, _, val, body) => {
                self.collect_q_pattern_vars(val, vars, seen);
                self.collect_q_pattern_vars(body, vars, seen);
            }

            // Leaf expressions - no pattern variables
            SurfaceExpr::Ident(..)
            | SurfaceExpr::SyntheticSorry(..)
            | SurfaceExpr::Universe(..)
            | SurfaceExpr::Lit(..)
            | SurfaceExpr::Hole(..) => {}

            // Other expressions - could be extended
            _ => {}
        })
    }
}
