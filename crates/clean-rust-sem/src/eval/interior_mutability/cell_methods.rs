// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::models::{InteriorCellState, OnceCellModel};
use super::Interpreter;
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::types::Mutability;
use crate::values::{RefCellBorrowState, Value};
use std::collections::BTreeMap;

impl Interpreter {
    fn interior_borrow_error_value(mutable: bool) -> Value {
        Value::Struct {
            name: if mutable {
                "BorrowMutError".to_string()
            } else {
                "BorrowError".to_string()
            },
            fields: BTreeMap::new(),
        }
    }

    fn borrow_conflict_message(mutable: bool, state: &RefCellBorrowState) -> &'static str {
        match (mutable, state) {
            (false, RefCellBorrowState::Mutable) => "RefCell already mutably borrowed",
            (true, RefCellBorrowState::Unborrowed) => unreachable!("caller should handle success"),
            (true, RefCellBorrowState::Mutable) => "RefCell already mutably borrowed",
            (true, RefCellBorrowState::Shared { .. }) => "RefCell already borrowed",
            (false, RefCellBorrowState::Unborrowed | RefCellBorrowState::Shared { .. }) => {
                unreachable!("caller should handle success")
            }
        }
    }

    pub(super) fn eval_cell_method(&mut self, id: u64, method: &str, args: &[Value]) -> EvalResult {
        match method {
            "get" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("get", 0, args.len()).to_string(),
                    );
                }
                match self.read_interior_cell_value(id) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }
            "set" => {
                if args.len() != 1 {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("set", 1, args.len()).to_string(),
                    );
                }
                match self.write_interior_cell_value(id, args[0].clone()) {
                    Ok(()) => EvalResult::Value(Value::Unit),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }
            "replace" => {
                if args.len() != 1 {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("replace", 1, args.len()).to_string(),
                    );
                }
                let current = match self.read_interior_cell_value(id) {
                    Ok(value) => value,
                    Err(err) => return EvalResult::Error(err.to_string()),
                };
                match self.write_interior_cell_value(id, args[0].clone()) {
                    Ok(()) => EvalResult::Value(current),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }
            _ => EvalResult::Error(format!("undefined Cell method `{method}`")),
        }
    }

    fn eval_refcell_borrow(&mut self, id: u64, mutable: bool, fallible: bool) -> EvalResult {
        let (current_value, borrow_state) = match self.interior_cells.get(&id) {
            Some(InteriorCellState::RefCell { value, borrow }) => {
                (self.materialize_value(value), borrow.clone())
            }
            Some(_) => {
                return EvalResult::Error(format!("interior cell `{id}` is not a RefCell"));
            }
            None => {
                return EvalResult::Error(format!("unknown interior cell `{id}`"));
            }
        };

        let new_state = match (mutable, &borrow_state) {
            (false, RefCellBorrowState::Unborrowed) => RefCellBorrowState::Shared { count: 1 },
            (false, RefCellBorrowState::Shared { count }) => {
                RefCellBorrowState::Shared { count: count + 1 }
            }
            (true, RefCellBorrowState::Unborrowed) => RefCellBorrowState::Mutable,
            _ => {
                if fallible {
                    return EvalResult::Value(Self::result_value(Err(
                        Self::interior_borrow_error_value(mutable),
                    )));
                }
                return EvalResult::Error(
                    crate::eval::error::EvalError::BorrowError {
                        kind: if mutable
                            && matches!(borrow_state, RefCellBorrowState::Shared { .. })
                        {
                            "refcell_already_borrowed".to_string()
                        } else {
                            "refcell_already_mutably_borrowed".to_string()
                        },
                        context: Self::borrow_conflict_message(mutable, &borrow_state).to_string(),
                    }
                    .to_string(),
                );
            }
        };

        if let Some(InteriorCellState::RefCell { borrow, .. }) = self.interior_cells.get_mut(&id) {
            *borrow = new_state;
        }

        let guard = if mutable {
            Value::RefCellRefMut {
                cell_id: id,
                value: Box::new(current_value),
            }
        } else {
            Value::RefCellRef {
                cell_id: id,
                value: Box::new(current_value),
            }
        };

        if fallible {
            EvalResult::Value(Self::result_value(Ok(guard)))
        } else {
            EvalResult::Value(guard)
        }
    }

    pub(super) fn eval_refcell_method(
        &mut self,
        id: u64,
        method: &str,
        args: &[Value],
    ) -> EvalResult {
        match method {
            "borrow" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("borrow", 0, args.len()).to_string(),
                    );
                }
                self.eval_refcell_borrow(id, false, false)
            }
            "borrow_mut" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("borrow_mut", 0, args.len()).to_string(),
                    );
                }
                self.eval_refcell_borrow(id, true, false)
            }
            "try_borrow" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("try_borrow", 0, args.len()).to_string(),
                    );
                }
                self.eval_refcell_borrow(id, false, true)
            }
            "try_borrow_mut" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("try_borrow_mut", 0, args.len()).to_string(),
                    );
                }
                self.eval_refcell_borrow(id, true, true)
            }
            _ => EvalResult::Error(format!("undefined RefCell method `{method}`")),
        }
    }

    fn eval_once_cell_set(&mut self, id: u64, method: &str, value: Value) -> EvalResult {
        let materialized = self.materialize_value(&value);
        let Some(state) = self.interior_cells.get_mut(&id) else {
            return EvalResult::Error(format!("unknown interior cell `{id}`"));
        };
        match state {
            InteriorCellState::OnceCell(OnceCellModel { value: slot })
            | InteriorCellState::OnceLock(OnceCellModel { value: slot }) => {
                if slot.is_some() {
                    EvalResult::Value(Self::result_value(Err(value)))
                } else {
                    *slot = Some(materialized);
                    EvalResult::Value(Self::result_value(Ok(Value::Unit)))
                }
            }
            _ => EvalResult::Error(format!(
                "undefined {method} receiver for interior cell `{id}`"
            )),
        }
    }

    fn eval_once_cell_get(&mut self, id: u64) -> EvalResult {
        let Some(state) = self.interior_cells.get(&id) else {
            return EvalResult::Error(format!("unknown interior cell `{id}`"));
        };
        let value = match state {
            InteriorCellState::OnceCell(OnceCellModel { value })
            | InteriorCellState::OnceLock(OnceCellModel { value }) => {
                value.as_ref().map(|value| self.materialize_value(value))
            }
            _ => return EvalResult::Error(format!("interior cell `{id}` is not a once cell")),
        };
        match value {
            Some(value) => match self.preserved_reference(value, Mutability::Shared) {
                Ok(reference) => EvalResult::Value(Self::option_value(Some(reference))),
                Err(err) => EvalResult::Error(err.to_string()),
            },
            None => EvalResult::Value(Self::option_value(None)),
        }
    }

    fn eval_once_cell_get_or_init(&mut self, id: u64, init: &Value, method: &str) -> EvalResult {
        if let Some(value) = self.interior_cells.get(&id).and_then(|state| match state {
            InteriorCellState::OnceCell(OnceCellModel { value })
            | InteriorCellState::OnceLock(OnceCellModel { value }) => value.clone(),
            _ => None,
        }) {
            return match self.preserved_reference(value, Mutability::Shared) {
                Ok(reference) => EvalResult::Value(reference),
                Err(err) => EvalResult::Error(err.to_string()),
            };
        }

        match self.call_callable_value(init, vec![], &[]) {
            EvalResult::Value(value) => {
                let materialized = self.materialize_value(&value);
                if let Some(state) = self.interior_cells.get_mut(&id) {
                    match state {
                        InteriorCellState::OnceCell(OnceCellModel { value: slot })
                        | InteriorCellState::OnceLock(OnceCellModel { value: slot }) => {
                            if slot.is_none() {
                                *slot = Some(materialized.clone());
                            }
                        }
                        _ => {
                            return EvalResult::Error(format!(
                                "undefined {method} receiver for interior cell `{id}`"
                            ));
                        }
                    }
                }
                match self.preserved_reference(materialized, Mutability::Shared) {
                    Ok(reference) => EvalResult::Value(reference),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }
            other => other,
        }
    }

    pub(super) fn eval_once_cell_method(
        &mut self,
        id: u64,
        method: &str,
        args: &[Value],
    ) -> EvalResult {
        match method {
            "get" => {
                if !args.is_empty() {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("get", 0, args.len()).to_string(),
                    );
                }
                self.eval_once_cell_get(id)
            }
            "set" => {
                if args.len() != 1 {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("set", 1, args.len()).to_string(),
                    );
                }
                self.eval_once_cell_set(id, method, args[0].clone())
            }
            "get_or_init" => {
                if args.len() != 1 {
                    return EvalResult::Error(
                        RustSemError::intrinsic_arity("get_or_init", 1, args.len()).to_string(),
                    );
                }
                self.eval_once_cell_get_or_init(id, &args[0], method)
            }
            _ => EvalResult::Error(format!("undefined OnceCell method `{method}`")),
        }
    }
}
