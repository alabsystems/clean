// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory article-level types.

use super::name::OtName;
use super::term::OtTheorem;
use super::vm::OtContext;

/// Parsed and executed OpenTheory article.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtArticle {
    pub version: u32,
    pub commands: Vec<OtCommand>,
    pub assumptions: Vec<OtTheorem>,
    pub theorems: Vec<OtTheorem>,
}

impl OtArticle {
    /// Collect proved theorems into a context map for use by downstream articles.
    ///
    /// Each theorem is keyed by its `(hypotheses, conclusion)` pair so that
    /// when a downstream article uses `axiom` with matching hypotheses and
    /// conclusion, the VM can substitute the proved theorem instead of
    /// creating an unresolved assumption.
    #[must_use]
    pub fn proved_theorems_as_context(&self) -> OtContext {
        let mut context = OtContext::default();
        for theorem in &self.theorems {
            let key = (theorem.hypotheses.clone(), theorem.conclusion.clone());
            context.insert(key, theorem.clone());
        }
        context
    }
}

/// One OpenTheory article command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtCommand {
    Number(i64),
    Name(OtName),
    AbsTerm,
    AbsThm,
    AppTerm,
    AppThm,
    Assume,
    Axiom,
    BetaConv,
    Cons,
    Const,
    ConstTerm,
    DeductAntisym,
    Def,
    DefineConst,
    DefineConstList,
    DefineTypeOp,
    EqMp,
    HdTl,
    Nil,
    OpType,
    Pop,
    Pragma,
    ProveHyp,
    Ref,
    Refl,
    Remove,
    Subst,
    Sym,
    Thm,
    Trans,
    TypeOp,
    Var,
    VarTerm,
    VarType,
    Version,
}
