// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod cell_methods;
mod lock_methods;
mod models;

use super::Interpreter;
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::values::{EnumPayload, RefCellBorrowState, Value};
pub(crate) use models::InteriorCellState;
use models::{InteriorCellKind, MutexModel, OnceCellModel, RwLockModel, UnsafeCellModel};

impl Interpreter {
    fn fresh_interior_cell_id(&mut self) -> u64 {
        let id = self.next_interior_cell_id;
        self.next_interior_cell_id += 1;
        id
    }

    fn alloc_interior_cell(&mut self, kind: InteriorCellKind, value: Value) -> Value {
        let id = self.fresh_interior_cell_id();
        let value = self.materialize_value(&value);
        let state = match kind {
            InteriorCellKind::Cell => InteriorCellState::Cell {
                value: value.clone(),
            },
            InteriorCellKind::RefCell => InteriorCellState::RefCell {
                value: value.clone(),
                borrow: RefCellBorrowState::Unborrowed,
            },
            InteriorCellKind::UnsafeCell => InteriorCellState::UnsafeCell(UnsafeCellModel {
                value: value.clone(),
            }),
            InteriorCellKind::OnceCell => InteriorCellState::OnceCell(OnceCellModel {
                value: Some(value.clone()),
            }),
            InteriorCellKind::OnceLock => InteriorCellState::OnceLock(OnceCellModel {
                value: Some(value.clone()),
            }),
            InteriorCellKind::Mutex => InteriorCellState::Mutex(MutexModel {
                value: value.clone(),
                locked: false,
                poisoned: false,
            }),
            InteriorCellKind::RwLock => InteriorCellState::RwLock(RwLockModel {
                value: value.clone(),
                reader_count: 0,
                writer_locked: false,
                poisoned: false,
            }),
        };
        self.interior_cells.insert(id, state);
        self.materialize_interior_cell(id)
            .expect("fresh interior cell should materialize")
    }

    fn alloc_empty_once_cell(&mut self, kind: InteriorCellKind) -> Value {
        let id = self.fresh_interior_cell_id();
        let state = match kind {
            InteriorCellKind::OnceCell => {
                InteriorCellState::OnceCell(OnceCellModel { value: None })
            }
            InteriorCellKind::OnceLock => {
                InteriorCellState::OnceLock(OnceCellModel { value: None })
            }
            _ => unreachable!("only once-cell kinds may be empty"),
        };
        self.interior_cells.insert(id, state);
        self.materialize_interior_cell(id)
            .expect("fresh empty once cell should materialize")
    }

    fn materialize_payload(&self, payload: &EnumPayload) -> EnumPayload {
        match payload {
            EnumPayload::Unit => EnumPayload::Unit,
            EnumPayload::Tuple(values) => EnumPayload::Tuple(
                values
                    .iter()
                    .map(|value| self.materialize_value(value))
                    .collect(),
            ),
            EnumPayload::Struct(fields) => EnumPayload::Struct(
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.materialize_value(value)))
                    .collect(),
            ),
        }
    }

    fn materialize_interior_cell(&self, id: u64) -> Result<Value, RustSemError> {
        let state = self
            .interior_cells
            .get(&id)
            .ok_or_else(|| RustSemError::Eval(format!("unknown interior cell `{id}`")))?;
        Ok(match state {
            InteriorCellState::Cell { value } => Value::Cell {
                id,
                value: Box::new(self.materialize_value(value)),
            },
            InteriorCellState::RefCell { value, borrow } => Value::RefCell {
                id,
                value: Box::new(self.materialize_value(value)),
                borrow: borrow.clone(),
            },
            InteriorCellState::UnsafeCell(model) => Value::UnsafeCell {
                id,
                value: Box::new(self.materialize_value(&model.value)),
            },
            InteriorCellState::OnceCell(model) => Value::OnceCell {
                id,
                value: model
                    .value
                    .as_ref()
                    .map(|value| Box::new(self.materialize_value(value))),
            },
            InteriorCellState::OnceLock(model) => Value::OnceLock {
                id,
                value: model
                    .value
                    .as_ref()
                    .map(|value| Box::new(self.materialize_value(value))),
            },
            InteriorCellState::Mutex(model) => Value::Mutex {
                id,
                value: Box::new(self.materialize_value(&model.value)),
                locked: model.locked,
                poisoned: model.poisoned,
            },
            InteriorCellState::RwLock(model) => Value::RwLock {
                id,
                value: Box::new(self.materialize_value(&model.value)),
                reader_count: model.reader_count,
                writer_locked: model.writer_locked,
                poisoned: model.poisoned,
            },
        })
    }

    pub(super) fn materialize_value(&self, value: &Value) -> Value {
        match value {
            Value::Reference {
                addr,
                mutability,
                lifetime,
                referent,
            } => Value::Reference {
                addr: *addr,
                mutability: *mutability,
                lifetime: lifetime.clone(),
                referent: referent
                    .as_ref()
                    .map(|value| Box::new(self.materialize_value(value))),
            },
            Value::Cell { id, .. }
            | Value::RefCell { id, .. }
            | Value::UnsafeCell { id, .. }
            | Value::OnceCell { id, .. }
            | Value::OnceLock { id, .. }
            | Value::Mutex { id, .. }
            | Value::RwLock { id, .. } => self
                .materialize_interior_cell(*id)
                .unwrap_or_else(|_| value.clone()),
            Value::RefCellRef { cell_id, value } => {
                let value = self
                    .read_interior_cell_value(*cell_id)
                    .unwrap_or_else(|_| self.materialize_value(value));
                Value::RefCellRef {
                    cell_id: *cell_id,
                    value: Box::new(value),
                }
            }
            Value::RefCellRefMut { cell_id, value } => {
                let value = self
                    .read_interior_cell_value(*cell_id)
                    .unwrap_or_else(|_| self.materialize_value(value));
                Value::RefCellRefMut {
                    cell_id: *cell_id,
                    value: Box::new(value),
                }
            }
            Value::MutexGuard { lock_id, value } => {
                let value = self
                    .read_interior_cell_value(*lock_id)
                    .unwrap_or_else(|_| self.materialize_value(value));
                Value::MutexGuard {
                    lock_id: *lock_id,
                    value: Box::new(value),
                }
            }
            Value::RwLockReadGuard { lock_id, value } => {
                let value = self
                    .read_interior_cell_value(*lock_id)
                    .unwrap_or_else(|_| self.materialize_value(value));
                Value::RwLockReadGuard {
                    lock_id: *lock_id,
                    value: Box::new(value),
                }
            }
            Value::RwLockWriteGuard { lock_id, value } => {
                let value = self
                    .read_interior_cell_value(*lock_id)
                    .unwrap_or_else(|_| self.materialize_value(value));
                Value::RwLockWriteGuard {
                    lock_id: *lock_id,
                    value: Box::new(value),
                }
            }
            Value::FatPtr(crate::values::FatPointer {
                data_pointer,
                metadata,
            }) => Value::FatPtr(crate::values::FatPointer {
                data_pointer: Box::new(self.materialize_value(data_pointer)),
                metadata: metadata.clone(),
            }),
            Value::Tuple(values) => Value::Tuple(
                values
                    .iter()
                    .map(|value| self.materialize_value(value))
                    .collect(),
            ),
            Value::Range {
                start,
                end,
                inclusive,
            } => Value::Range {
                start: start
                    .as_ref()
                    .map(|value| Box::new(self.materialize_value(value))),
                end: end
                    .as_ref()
                    .map(|value| Box::new(self.materialize_value(value))),
                inclusive: *inclusive,
            },
            Value::Array(values) => Value::Array(
                values
                    .iter()
                    .map(|value| self.materialize_value(value))
                    .collect(),
            ),
            Value::Struct { name, fields } => Value::Struct {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(field, value)| (field.clone(), self.materialize_value(value)))
                    .collect(),
            },
            Value::Enum {
                name,
                variant,
                payload,
            } => Value::Enum {
                name: name.clone(),
                variant: variant.clone(),
                payload: Box::new(self.materialize_payload(payload)),
            },
            Value::Union {
                name,
                active_field,
                value,
            } => Value::Union {
                name: name.clone(),
                active_field: active_field.clone(),
                value: Box::new(self.materialize_value(value)),
            },
            Value::Closure {
                fn_id,
                captures,
                param_types,
                ret_type,
                kind,
            } => Value::Closure {
                fn_id: fn_id.clone(),
                captures: captures
                    .iter()
                    .map(|(name, value, mutability)| {
                        (name.clone(), self.materialize_value(value), *mutability)
                    })
                    .collect(),
                param_types: param_types.clone(),
                ret_type: ret_type.clone(),
                kind: *kind,
            },
            Value::TraitObject {
                data,
                vtable,
                lifetime,
            } => Value::TraitObject {
                data: Box::new(self.materialize_value(data)),
                vtable: vtable.clone(),
                lifetime: lifetime.clone(),
            },
            _ => value.clone(),
        }
    }

    pub(super) fn read_interior_cell_value(&self, id: u64) -> Result<Value, RustSemError> {
        self.interior_cells
            .get(&id)
            .and_then(InteriorCellState::value)
            .map(|value| self.materialize_value(value))
            .ok_or_else(|| RustSemError::Eval(format!("unknown or empty interior cell `{id}`")))
    }

    pub(super) fn write_interior_cell_value(
        &mut self,
        id: u64,
        value: Value,
    ) -> Result<(), RustSemError> {
        let value = self.materialize_value(&value);
        let state = self
            .interior_cells
            .get_mut(&id)
            .ok_or_else(|| RustSemError::Eval(format!("unknown interior cell `{id}`")))?;
        let Some(slot) = state.value_mut() else {
            return Err(RustSemError::Eval(format!(
                "interior cell `{id}` does not expose a mutable inner value"
            )));
        };
        *slot = value;
        Ok(())
    }

    pub(in crate::eval) fn try_interior_mutability_intrinsic(
        &mut self,
        name: &str,
        args: &[Value],
    ) -> Option<Result<Value, RustSemError>> {
        match name {
            "Cell::new" if args.len() == 1 => Some(Ok(
                self.alloc_interior_cell(InteriorCellKind::Cell, args[0].clone())
            )),
            "RefCell::new" if args.len() == 1 => Some(Ok(
                self.alloc_interior_cell(InteriorCellKind::RefCell, args[0].clone())
            )),
            "UnsafeCell::new" if args.len() == 1 => Some(Ok(
                self.alloc_interior_cell(InteriorCellKind::UnsafeCell, args[0].clone())
            )),
            "OnceCell::new" if args.is_empty() => {
                Some(Ok(self.alloc_empty_once_cell(InteriorCellKind::OnceCell)))
            }
            "OnceLock::new" if args.is_empty() => {
                Some(Ok(self.alloc_empty_once_cell(InteriorCellKind::OnceLock)))
            }
            "Mutex::new" if args.len() == 1 => Some(Ok(
                self.alloc_interior_cell(InteriorCellKind::Mutex, args[0].clone())
            )),
            "RwLock::new" if args.len() == 1 => Some(Ok(
                self.alloc_interior_cell(InteriorCellKind::RwLock, args[0].clone())
            )),
            _ => None,
        }
    }

    pub(in crate::eval) fn is_interior_mutability_intrinsic_function_name(name: &str) -> bool {
        matches!(
            name,
            "Cell::new"
                | "RefCell::new"
                | "UnsafeCell::new"
                | "OnceCell::new"
                | "OnceLock::new"
                | "Mutex::new"
                | "RwLock::new"
        )
    }

    pub(in crate::eval) fn try_interior_mutability_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        let materialized = self.materialize_value(receiver);
        match materialized.deref_view() {
            Value::Cell { id, .. } => Some(self.eval_cell_method(*id, method, args)),
            Value::RefCell { id, .. } => Some(self.eval_refcell_method(*id, method, args)),
            Value::OnceCell { id, .. } | Value::OnceLock { id, .. } => {
                Some(self.eval_once_cell_method(*id, method, args))
            }
            Value::Mutex { id, .. } => Some(self.eval_mutex_method(*id, method, args)),
            Value::RwLock { id, .. } => Some(self.eval_rwlock_method(*id, method, args)),
            _ => None,
        }
    }
}
