// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion layer from `tla-core`'s canonical AST into clean-tla's local
//! types ([`TlaExpr`], [`TlaFormula`], [`TlaOperator`], [`TlaDeclare`]).
//!
//! This module is the single source of truth for the mapping between
//! `tla_core::ast::Expr` and clean-tla's parallel AST. See the mapping tables
//! on [`TlaExpr`] and [`TlaFormula`] for the variant-by-variant correspondence.
//!
//! New callers should prefer the [`TryFrom`] impls on [`TlaExpr`], [`TlaFormula`],
//! and [`TlaOperator`] rather than constructing clean-tla types directly.
//!
//! # Why a separate AST exists (for now)
//!
//! 1. **Serialization**: `TlaExpr`/`TlaFormula` derive `Serialize`/`Deserialize`
//!    for the obligation wire format. `tla_core::ast::Expr` does not.
//! 2. **Formula/Expression split**: TLA+ does not distinguish propositions from
//!    values, but the clean encoding needs to (Prop vs TLA.Value). The local
//!    `TlaFormula` type captures this split.
//! 3. **Lossy narrowing**: `tla_core::ast::Expr` carries spans and uses `BigInt`;
//!    clean-tla drops spans and narrows to `i64`.
//!
//! # Migration path
//!
//! When tla-core gains serde support or clean-tla can accept `tla_core::ast::Expr`
//! directly, this module and the local AST types should be removed. See #2468.

use crate::encoding::{TlaExpr, TlaFormula, TlaOperator};
use crate::obligation::TlaDeclare;
use crate::tla_core::ast as core_ast;
use crate::tla_core::Spanned;
use crate::TlaError;

mod expr;
mod formula;
mod shared;
mod tuple_pattern;

#[cfg(test)]
mod tests;

impl TlaExpr {
    /// Convert a canonical `tla-core` AST node into the current clean-tla value
    /// expression surface.
    pub fn from_tla_core(expr: &Spanned<core_ast::Expr>) -> Result<Self, TlaError> {
        expr::expr_from_core(expr)
    }
}

impl TlaFormula {
    /// Convert a canonical `tla-core` AST node into the current clean-tla
    /// propositional surface.
    pub fn from_tla_core(expr: &Spanned<core_ast::Expr>) -> Result<Self, TlaError> {
        formula::formula_from_core(expr)
    }
}

impl TlaOperator {
    /// Convert a canonical `tla-core` operator definition into the current
    /// clean-tla wire surface.
    pub fn from_tla_core(op: &core_ast::OperatorDef) -> Result<Self, TlaError> {
        Ok(Self {
            name: op.name.node.clone(),
            params: op
                .params
                .iter()
                .map(|param| param.name.node.clone())
                .collect(),
            body: expr::expr_from_core(&op.body)?,
        })
    }
}

impl TlaDeclare {
    /// Convert a `tla-core` module unit into zero or more obligation
    /// declarations.
    pub fn from_tla_core_unit(unit: &core_ast::Unit) -> Result<Vec<Self>, TlaError> {
        match unit {
            core_ast::Unit::Variable(vars) => Ok(vars
                .iter()
                .map(|name| Self::Variable {
                    name: name.node.clone(),
                })
                .collect()),
            core_ast::Unit::Constant(constants) => Ok(constants
                .iter()
                .map(|decl| Self::Constant {
                    name: decl.name.node.clone(),
                    arity: decl.arity.unwrap_or(0) as u32,
                })
                .collect()),
            core_ast::Unit::Operator(op) => Ok(vec![Self::Operator {
                name: op.name.node.clone(),
                params: op
                    .params
                    .iter()
                    .map(|param| param.name.node.clone())
                    .collect(),
                body: TlaExpr::from_tla_core(&op.body)?,
            }]),
            core_ast::Unit::Assume(assume) => Ok(vec![Self::Assume {
                name: assume
                    .name
                    .as_ref()
                    .map(|name| name.node.clone())
                    .unwrap_or_else(|| "_ASSUME".to_string()),
                formula: TlaFormula::from_tla_core(&assume.expr)?,
            }]),
            core_ast::Unit::Instance(inst) => Ok(vec![Self::Instance {
                module: inst.module.node.clone(),
                substitutions: inst
                    .substitutions
                    .iter()
                    .map(|sub| Ok((sub.from.node.clone(), TlaExpr::from_tla_core(&sub.to)?)))
                    .collect::<Result<Vec<_>, TlaError>>()?,
            }]),
            core_ast::Unit::Recursive(_)
            | core_ast::Unit::Theorem(_)
            | core_ast::Unit::Separator => Ok(Vec::new()),
        }
    }
}
