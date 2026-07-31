// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::values::{Ordering, Value};
use std::fmt;

/// Memory ordering accepted by the atomic evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl MemoryOrdering {
    pub const fn has_acquire_semantics(self) -> bool {
        matches!(self, Self::Acquire | Self::AcqRel | Self::SeqCst)
    }

    pub const fn has_release_semantics(self) -> bool {
        matches!(self, Self::Release | Self::AcqRel | Self::SeqCst)
    }

    const fn permits_load(self) -> bool {
        !matches!(self, Self::Release | Self::AcqRel)
    }

    const fn permits_store(self) -> bool {
        !matches!(self, Self::Acquire | Self::AcqRel)
    }

    const fn permits_fence(self) -> bool {
        !matches!(self, Self::Relaxed)
    }

    const fn compare_exchange_failure_allowed(self, failure: Self) -> bool {
        match self {
            Self::Relaxed => matches!(failure, Self::Relaxed),
            Self::Acquire => matches!(failure, Self::Relaxed | Self::Acquire),
            Self::Release => matches!(failure, Self::Relaxed),
            Self::AcqRel => matches!(failure, Self::Relaxed | Self::Acquire),
            Self::SeqCst => matches!(failure, Self::Relaxed | Self::Acquire | Self::SeqCst),
        }
    }
}

impl From<Ordering> for MemoryOrdering {
    fn from(value: Ordering) -> Self {
        match value {
            Ordering::Relaxed => Self::Relaxed,
            Ordering::Acquire => Self::Acquire,
            Ordering::Release => Self::Release,
            Ordering::AcqRel => Self::AcqRel,
            Ordering::SeqCst => Self::SeqCst,
        }
    }
}

impl TryFrom<&Value> for MemoryOrdering {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        Ordering::from_value(value)
            .map(Self::from)
            .ok_or_else(|| "expected atomic memory ordering".to_string())
    }
}

/// Atomic operations supported by the evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicOp {
    Load,
    Store,
    Swap,
    CompareExchange,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
}

impl AtomicOp {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Load => "load",
            Self::Store => "store",
            Self::Swap => "swap",
            Self::CompareExchange => "compare_exchange",
            Self::FetchAdd => "fetch_add",
            Self::FetchSub => "fetch_sub",
            Self::FetchAnd => "fetch_and",
            Self::FetchOr => "fetch_or",
            Self::FetchXor => "fetch_xor",
        }
    }
}

/// Fence intrinsics supported by the evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicFenceKind {
    Fence,
    CompilerFence,
}

impl AtomicFenceKind {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Fence => "fence",
            Self::CompilerFence => "compiler_fence",
        }
    }
}

/// Model of a fence operation with its ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtomicFence {
    kind: AtomicFenceKind,
    ordering: MemoryOrdering,
}

impl AtomicFence {
    pub const fn new(ordering: MemoryOrdering) -> Self {
        Self::with_kind(AtomicFenceKind::Fence, ordering)
    }

    pub const fn compiler(ordering: MemoryOrdering) -> Self {
        Self::with_kind(AtomicFenceKind::CompilerFence, ordering)
    }

    pub const fn with_kind(kind: AtomicFenceKind, ordering: MemoryOrdering) -> Self {
        Self { kind, ordering }
    }

    pub const fn kind(self) -> AtomicFenceKind {
        self.kind
    }

    pub const fn ordering(self) -> MemoryOrdering {
        self.ordering
    }

    pub const fn has_acquire_semantics(self) -> bool {
        self.ordering.has_acquire_semantics()
    }

    pub const fn has_release_semantics(self) -> bool {
        self.ordering.has_release_semantics()
    }

    pub fn validate(self) -> Result<(), String> {
        validate_fence_ordering(self)
    }
}

/// Ordering violation gathered while validating atomic operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomicOrderingViolation {
    InvalidOperationOrdering {
        op: AtomicOp,
        ordering: MemoryOrdering,
    },
    InvalidFenceOrdering {
        kind: AtomicFenceKind,
        ordering: MemoryOrdering,
    },
    CompareExchangeFailureTooStrong {
        success: MemoryOrdering,
        failure: MemoryOrdering,
    },
    SameThreadSynchronization {
        thread_id: usize,
    },
    SynchronizationSourceMissingRelease {
        thread_id: usize,
        ordering: MemoryOrdering,
    },
    SynchronizationTargetMissingAcquire {
        thread_id: usize,
        ordering: MemoryOrdering,
    },
}

impl fmt::Display for AtomicOrderingViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOperationOrdering { op, ordering } => {
                write!(
                    f,
                    "atomic {} does not permit `{:?}` ordering",
                    op.name(),
                    ordering
                )
            }
            Self::InvalidFenceOrdering { kind, ordering } => {
                write!(
                    f,
                    "atomic {} does not permit `{:?}` ordering",
                    kind.name(),
                    ordering
                )
            }
            Self::CompareExchangeFailureTooStrong { success, failure } => write!(
                f,
                "atomic compare_exchange failure ordering `{:?}` cannot be stronger than success ordering `{:?}`",
                failure, success
            ),
            Self::SameThreadSynchronization { thread_id } => write!(
                f,
                "happens-before edge must connect different threads (thread {thread_id})"
            ),
            Self::SynchronizationSourceMissingRelease { thread_id, ordering } => write!(
                f,
                "cross-thread synchronization source on thread {thread_id} needs release ordering, found `{:?}`",
                ordering
            ),
            Self::SynchronizationTargetMissingAcquire { thread_id, ordering } => write!(
                f,
                "cross-thread synchronization target on thread {thread_id} needs acquire ordering, found `{:?}`",
                ordering
            ),
        }
    }
}

/// Summary of one or more ordering validation failures.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AtomicOrderingReport {
    violations: Vec<AtomicOrderingViolation>,
}

impl AtomicOrderingReport {
    pub fn push(&mut self, violation: AtomicOrderingViolation) {
        self.violations.push(violation);
    }

    pub fn extend(&mut self, other: Self) {
        self.violations.extend(other.violations);
    }

    pub fn is_valid(&self) -> bool {
        self.violations.is_empty()
    }

    pub fn violations(&self) -> &[AtomicOrderingViolation] {
        &self.violations
    }

    pub fn summary(&self) -> String {
        match self.violations.as_slice() {
            [] => "no atomic ordering violations".to_string(),
            [violation] => violation.to_string(),
            violations => format!(
                "{} atomic ordering violations: {}",
                violations.len(),
                violations
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
        }
    }

    pub fn into_result(self) -> Result<(), String> {
        if self.is_valid() {
            Ok(())
        } else {
            Err(self.summary())
        }
    }
}

impl fmt::Display for AtomicOrderingReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.summary())
    }
}

/// Validate a single ordering argument for an atomic operation.
pub fn validate_ordering(op: AtomicOp, ordering: MemoryOrdering) -> Result<(), String> {
    let mut report = AtomicOrderingReport::default();
    let invalid = match op {
        AtomicOp::Load => !ordering.permits_load(),
        AtomicOp::Store => !ordering.permits_store(),
        AtomicOp::Swap
        | AtomicOp::CompareExchange
        | AtomicOp::FetchAdd
        | AtomicOp::FetchSub
        | AtomicOp::FetchAnd
        | AtomicOp::FetchOr
        | AtomicOp::FetchXor => false,
    };
    if invalid {
        report.push(AtomicOrderingViolation::InvalidOperationOrdering { op, ordering });
    }
    report.into_result()
}

pub fn validate_fence_ordering(fence: AtomicFence) -> Result<(), String> {
    let mut report = AtomicOrderingReport::default();
    if !fence.ordering().permits_fence() {
        report.push(AtomicOrderingViolation::InvalidFenceOrdering {
            kind: fence.kind(),
            ordering: fence.ordering(),
        });
    }
    report.into_result()
}

pub fn validate_compare_exchange_failure_ordering(
    success: MemoryOrdering,
    failure: MemoryOrdering,
) -> Result<(), String> {
    validate_ordering(AtomicOp::Load, failure)?;

    let mut report = AtomicOrderingReport::default();
    if !success.compare_exchange_failure_allowed(failure) {
        report.push(AtomicOrderingViolation::CompareExchangeFailureTooStrong { success, failure });
    }
    report.into_result()
}

pub fn validate_synchronizes_with(
    source_thread: usize,
    source: MemoryOrdering,
    target_thread: usize,
    target: MemoryOrdering,
) -> AtomicOrderingReport {
    let mut report = AtomicOrderingReport::default();
    if source_thread == target_thread {
        report.push(AtomicOrderingViolation::SameThreadSynchronization {
            thread_id: source_thread,
        });
    }
    if !source.has_release_semantics() {
        report.push(
            AtomicOrderingViolation::SynchronizationSourceMissingRelease {
                thread_id: source_thread,
                ordering: source,
            },
        );
    }
    if !target.has_acquire_semantics() {
        report.push(
            AtomicOrderingViolation::SynchronizationTargetMissingAcquire {
                thread_id: target_thread,
                ordering: target,
            },
        );
    }
    report
}

#[cfg(test)]
mod tests {
    use super::{
        validate_compare_exchange_failure_ordering, validate_fence_ordering, validate_ordering,
        validate_synchronizes_with, AtomicFence, AtomicFenceKind, AtomicOp, AtomicOrderingReport,
        AtomicOrderingViolation, MemoryOrdering,
    };

    #[test]
    fn validate_ordering_rejects_release_load() {
        assert_eq!(
            validate_ordering(AtomicOp::Load, MemoryOrdering::Release),
            Err("atomic load does not permit `Release` ordering".to_string())
        );
    }

    #[test]
    fn validate_ordering_rejects_acquire_store() {
        assert_eq!(
            validate_ordering(AtomicOp::Store, MemoryOrdering::Acquire),
            Err("atomic store does not permit `Acquire` ordering".to_string())
        );
    }

    #[test]
    fn compare_exchange_failure_rejects_release() {
        assert_eq!(
            validate_compare_exchange_failure_ordering(
                MemoryOrdering::SeqCst,
                MemoryOrdering::Release
            ),
            Err("atomic load does not permit `Release` ordering".to_string())
        );
    }

    #[test]
    fn compare_exchange_failure_must_not_be_stronger_than_success() {
        assert_eq!(
            validate_compare_exchange_failure_ordering(
                MemoryOrdering::Relaxed,
                MemoryOrdering::Acquire
            ),
            Err(
                "atomic compare_exchange failure ordering `Acquire` cannot be stronger than success ordering `Relaxed`"
                    .to_string()
            )
        );
    }

    #[test]
    fn fence_rejects_relaxed_ordering() {
        let fence = AtomicFence::with_kind(AtomicFenceKind::CompilerFence, MemoryOrdering::Relaxed);
        assert_eq!(
            validate_fence_ordering(fence),
            Err("atomic compiler_fence does not permit `Relaxed` ordering".to_string())
        );
    }

    #[test]
    fn report_summary_batches_multiple_violations() {
        let mut report = AtomicOrderingReport::default();
        report.push(AtomicOrderingViolation::InvalidOperationOrdering {
            op: AtomicOp::Load,
            ordering: MemoryOrdering::Release,
        });
        report.extend(validate_synchronizes_with(
            0,
            MemoryOrdering::Relaxed,
            1,
            MemoryOrdering::Relaxed,
        ));
        assert_eq!(
            report.summary(),
            "3 atomic ordering violations: atomic load does not permit `Release` ordering; cross-thread synchronization source on thread 0 needs release ordering, found `Relaxed`; cross-thread synchronization target on thread 1 needs acquire ordering, found `Relaxed`"
        );
    }
}
