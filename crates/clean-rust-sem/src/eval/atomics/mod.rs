// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod graph;
mod model;
mod runtime;
#[cfg(test)]
mod runtime_tests;

pub use graph::{AtomicEvent, AtomicEventId, AtomicEventKind, HappensBeforeGraph};
pub use model::{
    validate_compare_exchange_failure_ordering, validate_fence_ordering, validate_ordering,
    validate_synchronizes_with, AtomicFence, AtomicFenceKind, AtomicOp, AtomicOrderingReport,
    AtomicOrderingViolation, MemoryOrdering,
};
pub use runtime::eval_atomic_op;
