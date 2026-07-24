// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB2 AST types.
//!
//! Represents the structural content of `.smt2` files using the SMT-LIB2
//! standard S-expression format. Covers sorts, terms, and commands for
//! the core theory and common extensions (QF_LIA, QF_LRA, QF_BV, etc.).

use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Sorts
// ════════════════════════════════════════════════════════════════════════════

/// An SMT-LIB2 sort (type).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SmtSort {
    /// `Bool`
    Bool,
    /// `Int`
    Int,
    /// `Real`
    Real,
    /// `BitVec N`
    BitVec(u32),
    /// `Array` sort: `(Array index_sort elem_sort)`
    Array(Box<SmtSort>, Box<SmtSort>),
    /// Named sort (user-defined or uninterpreted).
    Named(String),
    /// Parameterized sort application: `(SortName Sort1 Sort2 ...)`
    App(String, Vec<SmtSort>),
}

// ════════════════════════════════════════════════════════════════════════════
// Terms
// ════════════════════════════════════════════════════════════════════════════

/// An SMT-LIB2 term (expression).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SmtTerm {
    /// Integer literal.
    IntLit(i64),
    /// Real literal (represented as numerator/denominator for rationals).
    RealLit(String),
    /// Boolean literal.
    BoolLit(bool),
    /// Bitvector literal: `#b0101` or `#x1F`.
    BvLit(String),
    /// String literal.
    StringLit(String),
    /// Symbol (variable or constant reference).
    Symbol(String),
    /// Function/operator application: `(f arg1 arg2 ...)`.
    App(String, Vec<SmtTerm>),
    /// `(let ((x t1) (y t2)) body)`
    Let(Vec<(String, SmtTerm)>, Box<SmtTerm>),
    /// `(forall ((x Sort) (y Sort)) body)`
    Forall(Vec<(String, SmtSort)>, Box<SmtTerm>),
    /// `(exists ((x Sort) (y Sort)) body)`
    Exists(Vec<(String, SmtSort)>, Box<SmtTerm>),
    /// `(! term :named name)` — annotated term.
    Annotated(Box<SmtTerm>, Vec<(String, String)>),
}

// ════════════════════════════════════════════════════════════════════════════
// Commands
// ════════════════════════════════════════════════════════════════════════════

/// An SMT-LIB2 command.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SmtCommand {
    /// `(set-logic LOGIC)`
    SetLogic(String),
    /// `(declare-sort NAME ARITY)`
    DeclareSort(String, u32),
    /// `(define-sort NAME (PARAMS) SORT)`
    DefineSort(String, Vec<String>, SmtSort),
    /// `(declare-fun NAME (PARAM_SORTS) RETURN_SORT)`
    DeclareFun(String, Vec<SmtSort>, SmtSort),
    /// `(declare-const NAME SORT)`
    DeclareConst(String, SmtSort),
    /// `(define-fun NAME ((PARAM SORT) ...) RETURN_SORT BODY)`
    DefineFun(String, Vec<(String, SmtSort)>, SmtSort, SmtTerm),
    /// `(assert TERM)`
    Assert(SmtTerm),
    /// `(check-sat)`
    CheckSat,
    /// `(get-model)`, `(get-value ...)`, `(get-unsat-core)`, etc.
    GetInfo(String),
    /// `(push N)` / `(pop N)`
    Push(u32),
    Pop(u32),
    /// `(set-info :keyword value)`
    SetInfo(String, String),
    /// `(set-option :keyword value)`
    SetOption(String, String),
    /// `(exit)`
    Exit,
    /// Unknown or unsupported command.
    Unknown(String),
}

// ════════════════════════════════════════════════════════════════════════════
// Script
// ════════════════════════════════════════════════════════════════════════════

/// A parsed SMT-LIB2 script (one `.smt2` file).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtScript {
    /// The logic, if set.
    pub logic: Option<String>,
    /// All commands in order.
    pub commands: Vec<SmtCommand>,
}

impl SmtScript {
    /// Count assertions.
    #[must_use]
    pub fn assert_count(&self) -> usize {
        self.commands
            .iter()
            .filter(|c| matches!(c, SmtCommand::Assert(_)))
            .count()
    }

    /// Count declarations (declare-fun + declare-const + declare-sort).
    #[must_use]
    pub fn declaration_count(&self) -> usize {
        self.commands
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    SmtCommand::DeclareFun(..)
                        | SmtCommand::DeclareConst(..)
                        | SmtCommand::DeclareSort(..)
                )
            })
            .count()
    }

    /// Count definitions (define-fun + define-sort).
    #[must_use]
    pub fn definition_count(&self) -> usize {
        self.commands
            .iter()
            .filter(|c| matches!(c, SmtCommand::DefineFun(..) | SmtCommand::DefineSort(..)))
            .count()
    }

    /// Whether the script contains a `(check-sat)` command.
    #[must_use]
    pub fn has_check_sat(&self) -> bool {
        self.commands
            .iter()
            .any(|c| matches!(c, SmtCommand::CheckSat))
    }

    /// Whether the script has no commands.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }

    /// All declared function/constant names with their sorts.
    #[must_use]
    pub fn declared_names(&self) -> Vec<(&str, &SmtSort)> {
        let mut names = Vec::new();
        for cmd in &self.commands {
            match cmd {
                SmtCommand::DeclareFun(name, _, ret) => names.push((name.as_str(), ret)),
                SmtCommand::DeclareConst(name, sort) => names.push((name.as_str(), sort)),
                _ => {}
            }
        }
        names
    }
}
