// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::models::{InteriorCellState, MutexModel, RwLockModel};
use super::Interpreter;
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::ownership::Place;
use crate::values::{EnumPayload, RefCellBorrowState, Value};
use std::collections::BTreeMap;

impl Interpreter {
    fn poison_error_value(guard: Value) -> Value {
        Value::Struct {
            name: "PoisonError".to_string(),
            fields: BTreeMap::from([("guard".to_string(), guard)]),
        }
    }

    fn try_lock_would_block_value() -> Value {
        Value::Enum {
            name: "TryLockError".to_string(),
            variant: "WouldBlock".to_string(),
            payload: Box::new(EnumPayload::Unit),
        }
    }

    fn try_lock_poisoned_value(guard: Value) -> Value {
        Value::Enum {
            name: "TryLockError".to_string(),
            variant: "Poisoned".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Self::poison_error_value(guard)])),
        }
    }

    fn mutex_guard_value(&self, id: u64) -> Result<Value, RustSemError> {
        let value = self.read_interior_cell_value(id)?;
        Ok(Value::MutexGuard {
            lock_id: id,
            value: Box::new(value),
        })
    }

    fn rwlock_guard_value(&self, id: u64, write: bool) -> Result<Value, RustSemError> {
        let value = self.read_interior_cell_value(id)?;
        Ok(if write {
            Value::RwLockWriteGuard {
                lock_id: id,
                value: Box::new(value),
            }
        } else {
            Value::RwLockReadGuard {
                lock_id: id,
                value: Box::new(value),
            }
        })
    }

    pub(super) fn eval_mutex_method(
        &mut self,
        id: u64,
        method: &str,
        args: &[Value],
    ) -> EvalResult {
        if !args.is_empty() {
            return EvalResult::Error(
                RustSemError::intrinsic_arity(method, 0, args.len()).to_string(),
            );
        }
        let (poisoned, locked) = match self.interior_cells.get(&id) {
            Some(InteriorCellState::Mutex(MutexModel {
                locked, poisoned, ..
            })) => (*poisoned, *locked),
            Some(_) => return EvalResult::Error(format!("interior cell `{id}` is not a Mutex")),
            None => return EvalResult::Error(format!("unknown interior cell `{id}`")),
        };

        match method {
            "lock" | "try_lock" => {
                if locked {
                    return if method == "try_lock" {
                        EvalResult::Value(Self::result_value(Err(
                            Self::try_lock_would_block_value(),
                        )))
                    } else {
                        EvalResult::Error(
                            "Mutex::lock would block on an already-locked mutex".to_string(),
                        )
                    };
                }
                if let Some(InteriorCellState::Mutex(model)) = self.interior_cells.get_mut(&id) {
                    model.locked = true;
                }
                let guard = match self.mutex_guard_value(id) {
                    Ok(guard) => guard,
                    Err(err) => return EvalResult::Error(err.to_string()),
                };
                if poisoned {
                    let err = if method == "try_lock" {
                        Self::try_lock_poisoned_value(guard)
                    } else {
                        Self::poison_error_value(guard)
                    };
                    EvalResult::Value(Self::result_value(Err(err)))
                } else {
                    EvalResult::Value(Self::result_value(Ok(guard)))
                }
            }
            _ => EvalResult::Error(format!("undefined Mutex method `{method}`")),
        }
    }

    pub(super) fn eval_rwlock_method(
        &mut self,
        id: u64,
        method: &str,
        args: &[Value],
    ) -> EvalResult {
        if !args.is_empty() {
            return EvalResult::Error(
                RustSemError::intrinsic_arity(method, 0, args.len()).to_string(),
            );
        }
        let (reader_count, writer_locked, poisoned) = match self.interior_cells.get(&id) {
            Some(InteriorCellState::RwLock(RwLockModel {
                reader_count,
                writer_locked,
                poisoned,
                ..
            })) => (*reader_count, *writer_locked, *poisoned),
            Some(_) => return EvalResult::Error(format!("interior cell `{id}` is not an RwLock")),
            None => return EvalResult::Error(format!("unknown interior cell `{id}`")),
        };

        let (write, fallible) = match method {
            "read" => (false, false),
            "try_read" => (false, true),
            "write" => (true, false),
            "try_write" => (true, true),
            _ => {
                return EvalResult::Error(format!("undefined RwLock method `{method}`"));
            }
        };

        let would_block = if write {
            writer_locked || reader_count > 0
        } else {
            writer_locked
        };
        if would_block {
            return if fallible {
                EvalResult::Value(Self::result_value(Err(Self::try_lock_would_block_value())))
            } else if write {
                EvalResult::Error("RwLock::write would block while the lock is held".to_string())
            } else {
                EvalResult::Error(
                    "RwLock::read would block while a writer holds the lock".to_string(),
                )
            };
        }

        if let Some(InteriorCellState::RwLock(model)) = self.interior_cells.get_mut(&id) {
            if write {
                model.writer_locked = true;
            } else {
                model.reader_count += 1;
            }
        }

        let guard = match self.rwlock_guard_value(id, write) {
            Ok(guard) => guard,
            Err(err) => return EvalResult::Error(err.to_string()),
        };
        if poisoned {
            let err = if fallible {
                Self::try_lock_poisoned_value(guard)
            } else {
                Self::poison_error_value(guard)
            };
            EvalResult::Value(Self::result_value(Err(err)))
        } else {
            EvalResult::Value(Self::result_value(Ok(guard)))
        }
    }

    pub(in crate::eval) fn release_interior_borrow_for_place(&mut self, place: &Place) {
        let Ok(value) = self.read_tracked_place_value(place) else {
            return;
        };
        let unwinding = self.is_unwinding_scope_drop();
        match value {
            Value::RefCellRef { cell_id, .. } => {
                if let Some(InteriorCellState::RefCell { borrow, .. }) =
                    self.interior_cells.get_mut(&cell_id)
                {
                    *borrow = match borrow {
                        RefCellBorrowState::Shared { count } if *count > 1 => {
                            RefCellBorrowState::Shared { count: *count - 1 }
                        }
                        _ => RefCellBorrowState::Unborrowed,
                    };
                }
            }
            Value::RefCellRefMut { cell_id, .. } => {
                if let Some(InteriorCellState::RefCell { borrow, .. }) =
                    self.interior_cells.get_mut(&cell_id)
                {
                    *borrow = RefCellBorrowState::Unborrowed;
                }
            }
            Value::MutexGuard { lock_id, .. } => {
                if let Some(InteriorCellState::Mutex(model)) = self.interior_cells.get_mut(&lock_id)
                {
                    model.locked = false;
                    if unwinding {
                        model.poisoned = true;
                    }
                }
            }
            Value::RwLockReadGuard { lock_id, .. } => {
                if let Some(InteriorCellState::RwLock(model)) =
                    self.interior_cells.get_mut(&lock_id)
                {
                    model.reader_count = model.reader_count.saturating_sub(1);
                }
            }
            Value::RwLockWriteGuard { lock_id, .. } => {
                if let Some(InteriorCellState::RwLock(model)) =
                    self.interior_cells.get_mut(&lock_id)
                {
                    model.writer_locked = false;
                    if unwinding {
                        model.poisoned = true;
                    }
                }
            }
            _ => {}
        }
    }
}
