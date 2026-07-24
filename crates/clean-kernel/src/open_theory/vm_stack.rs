// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory VM stack and bookkeeping helpers.

use super::name::OtName;
use super::object::OtObject;
use super::term::{OtConstant, OtTerm, OtTheorem, OtVariable};
use super::ty::{OtSymbolId, OtType, OtTypeOperator};
use super::vm::OtVmState;
use super::vm_support::expected_object;
use super::{OpenTheoryError, OpenTheoryResult};

impl OtVmState {
    pub(super) fn fresh_symbol_id(&mut self) -> OtSymbolId {
        let id = OtSymbolId(self.next_symbol_id);
        self.next_symbol_id += 1;
        id
    }

    pub(super) fn push_assumption(&mut self, theorem: OtTheorem) {
        if !self.assumptions.contains(&theorem) {
            self.assumptions.push(theorem);
        }
    }

    pub(super) fn push_theorem(&mut self, theorem: OtTheorem) {
        if !self.theorems.contains(&theorem) {
            self.theorems.push(theorem);
        }
    }

    pub(super) fn pop_obj(&mut self, command: &'static str) -> OpenTheoryResult<OtObject> {
        self.stack
            .pop()
            .ok_or(OpenTheoryError::StackUnderflow { command })
    }

    pub(super) fn pop_num(&mut self, command: &'static str) -> OpenTheoryResult<i64> {
        match self.pop_obj(command)? {
            OtObject::Num(value) => Ok(value),
            other => Err(expected_object(command, "number", &other)),
        }
    }

    pub(super) fn pop_name(&mut self, command: &'static str) -> OpenTheoryResult<OtName> {
        match self.pop_obj(command)? {
            OtObject::Name(name) => Ok(name),
            other => Err(expected_object(command, "name", &other)),
        }
    }

    pub(super) fn pop_list(&mut self, command: &'static str) -> OpenTheoryResult<Vec<OtObject>> {
        match self.pop_obj(command)? {
            OtObject::List(list) => Ok(list),
            other => Err(expected_object(command, "list", &other)),
        }
    }

    pub(super) fn pop_type_op(
        &mut self,
        command: &'static str,
    ) -> OpenTheoryResult<OtTypeOperator> {
        match self.pop_obj(command)? {
            OtObject::TypeOp(op) => Ok(op),
            other => Err(expected_object(command, "type operator", &other)),
        }
    }

    pub(super) fn pop_type(&mut self, command: &'static str) -> OpenTheoryResult<OtType> {
        match self.pop_obj(command)? {
            OtObject::Type(ty) => Ok(ty),
            other => Err(expected_object(command, "type", &other)),
        }
    }

    pub(super) fn pop_const(&mut self, command: &'static str) -> OpenTheoryResult<OtConstant> {
        match self.pop_obj(command)? {
            OtObject::Const(constant) => Ok(constant),
            other => Err(expected_object(command, "constant", &other)),
        }
    }

    pub(super) fn pop_var(&mut self, command: &'static str) -> OpenTheoryResult<OtVariable> {
        match self.pop_obj(command)? {
            OtObject::Var(variable) => Ok(variable),
            other => Err(expected_object(command, "variable", &other)),
        }
    }

    pub(super) fn pop_term(&mut self, command: &'static str) -> OpenTheoryResult<OtTerm> {
        match self.pop_obj(command)? {
            OtObject::Term(term) => Ok(term),
            other => Err(expected_object(command, "term", &other)),
        }
    }

    pub(super) fn pop_thm(&mut self, command: &'static str) -> OpenTheoryResult<OtTheorem> {
        match self.pop_obj(command)? {
            OtObject::Thm(theorem) => Ok(theorem),
            other => Err(expected_object(command, "theorem", &other)),
        }
    }

    pub(super) fn pop_term_list(&mut self, command: &'static str) -> OpenTheoryResult<Vec<OtTerm>> {
        self.pop_list(command)?
            .into_iter()
            .map(|object| match object {
                OtObject::Term(term) => Ok(term),
                other => Err(expected_object(command, "term", &other)),
            })
            .collect()
    }

    pub(super) fn pop_type_list(&mut self, command: &'static str) -> OpenTheoryResult<Vec<OtType>> {
        self.pop_list(command)?
            .into_iter()
            .map(|object| match object {
                OtObject::Type(ty) => Ok(ty),
                other => Err(expected_object(command, "type", &other)),
            })
            .collect()
    }

    pub(super) fn pop_name_list(&mut self, command: &'static str) -> OpenTheoryResult<Vec<OtName>> {
        self.pop_list(command)?
            .into_iter()
            .map(|object| match object {
                OtObject::Name(name) => Ok(name),
                other => Err(expected_object(command, "name", &other)),
            })
            .collect()
    }
}
