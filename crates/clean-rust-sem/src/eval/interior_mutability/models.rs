// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::values::{RefCellBorrowState, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InteriorCellKind {
    Cell,
    RefCell,
    UnsafeCell,
    OnceCell,
    OnceLock,
    Mutex,
    RwLock,
}

/// Raw interior-mutable storage behind an `UnsafeCell<T>`.
#[derive(Debug, Clone)]
pub(crate) struct UnsafeCellModel {
    pub(crate) value: Value,
}

/// Initialization-once storage behind `OnceCell<T>`/`OnceLock<T>`.
#[derive(Debug, Clone)]
pub(crate) struct OnceCellModel {
    pub(crate) value: Option<Value>,
}

/// Runtime lock state for `Mutex<T>`.
#[derive(Debug, Clone)]
pub(crate) struct MutexModel {
    pub(crate) value: Value,
    pub(crate) locked: bool,
    pub(crate) poisoned: bool,
}

/// Runtime lock state for `RwLock<T>`.
#[derive(Debug, Clone)]
pub(crate) struct RwLockModel {
    pub(crate) value: Value,
    pub(crate) reader_count: usize,
    pub(crate) writer_locked: bool,
    pub(crate) poisoned: bool,
}

#[derive(Debug, Clone)]
pub(crate) enum InteriorCellState {
    Cell {
        value: Value,
    },
    RefCell {
        value: Value,
        borrow: RefCellBorrowState,
    },
    UnsafeCell(UnsafeCellModel),
    OnceCell(OnceCellModel),
    OnceLock(OnceCellModel),
    Mutex(MutexModel),
    RwLock(RwLockModel),
}

impl InteriorCellState {
    pub(crate) fn value(&self) -> Option<&Value> {
        match self {
            Self::Cell { value } | Self::RefCell { value, .. } => Some(value),
            Self::UnsafeCell(model) => Some(&model.value),
            Self::OnceCell(model) | Self::OnceLock(model) => model.value.as_ref(),
            Self::Mutex(model) => Some(&model.value),
            Self::RwLock(model) => Some(&model.value),
        }
    }

    pub(crate) fn value_mut(&mut self) -> Option<&mut Value> {
        match self {
            Self::Cell { value } | Self::RefCell { value, .. } => Some(value),
            Self::UnsafeCell(model) => Some(&mut model.value),
            Self::OnceCell(_) | Self::OnceLock(_) => None,
            Self::Mutex(model) => Some(&mut model.value),
            Self::RwLock(model) => Some(&mut model.value),
        }
    }
}
