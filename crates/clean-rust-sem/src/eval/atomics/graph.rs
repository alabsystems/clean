// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

use super::model::{
    validate_fence_ordering, validate_ordering, validate_synchronizes_with, AtomicFence, AtomicOp,
    MemoryOrdering,
};
use std::collections::{BTreeSet, HashMap, VecDeque};

/// Stable handle for an event recorded in the happens-before graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomicEventId(usize);

impl AtomicEventId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Kind of event represented in the happens-before graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomicEventKind {
    Operation {
        op: AtomicOp,
        ordering: MemoryOrdering,
    },
    Fence(AtomicFence),
}

impl AtomicEventKind {
    fn ordering(&self) -> MemoryOrdering {
        match self {
            Self::Operation { ordering, .. } => *ordering,
            Self::Fence(fence) => fence.ordering(),
        }
    }
}

/// Atomic event with thread-local identity and ordering metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AtomicEvent {
    pub id: AtomicEventId,
    pub thread_id: usize,
    pub kind: AtomicEventKind,
}

impl AtomicEvent {
    pub fn ordering(&self) -> MemoryOrdering {
        self.kind.ordering()
    }
}

/// Minimal happens-before graph for atomic operations and fences.
#[derive(Debug, Clone, Default)]
pub struct HappensBeforeGraph {
    events: Vec<AtomicEvent>,
    edges: BTreeSet<(AtomicEventId, AtomicEventId)>,
    last_in_thread: HashMap<usize, AtomicEventId>,
}

impl HappensBeforeGraph {
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    pub fn len(&self) -> usize {
        self.events.len()
    }

    pub fn events(&self) -> &[AtomicEvent] {
        &self.events
    }

    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn has_edge(&self, source: AtomicEventId, target: AtomicEventId) -> bool {
        self.edges.contains(&(source, target))
    }

    pub fn event(&self, id: AtomicEventId) -> Option<&AtomicEvent> {
        self.events.get(id.index())
    }

    pub fn add_atomic_op(
        &mut self,
        thread_id: usize,
        op: AtomicOp,
        ordering: MemoryOrdering,
    ) -> Result<AtomicEventId, String> {
        validate_ordering(op, ordering)?;
        Ok(self.push_event(thread_id, AtomicEventKind::Operation { op, ordering }))
    }

    pub fn add_fence(
        &mut self,
        thread_id: usize,
        fence: AtomicFence,
    ) -> Result<AtomicEventId, String> {
        validate_fence_ordering(fence)?;
        Ok(self.push_event(thread_id, AtomicEventKind::Fence(fence)))
    }

    pub fn add_synchronizes_with(
        &mut self,
        source: AtomicEventId,
        target: AtomicEventId,
    ) -> Result<(), String> {
        let source_event = self
            .event(source)
            .ok_or_else(|| format!("unknown atomic event {}", source.index()))?;
        let target_event = self
            .event(target)
            .ok_or_else(|| format!("unknown atomic event {}", target.index()))?;
        validate_synchronizes_with(
            source_event.thread_id,
            source_event.ordering(),
            target_event.thread_id,
            target_event.ordering(),
        )
        .into_result()?;
        self.edges.insert((source, target));
        Ok(())
    }

    pub fn happens_before(&self, source: AtomicEventId, target: AtomicEventId) -> bool {
        if source == target || self.event(source).is_none() || self.event(target).is_none() {
            return false;
        }

        let mut queue = VecDeque::from([source]);
        let mut visited = BTreeSet::new();
        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            for &(edge_source, edge_target) in &self.edges {
                if edge_source == current {
                    if edge_target == target {
                        return true;
                    }
                    queue.push_back(edge_target);
                }
            }
        }
        false
    }

    fn push_event(&mut self, thread_id: usize, kind: AtomicEventKind) -> AtomicEventId {
        let id = AtomicEventId(self.events.len());
        if let Some(previous) = self.last_in_thread.insert(thread_id, id) {
            self.edges.insert((previous, id));
        }
        self.events.push(AtomicEvent {
            id,
            thread_id,
            kind,
        });
        id
    }
}

#[cfg(test)]
mod tests {
    use super::HappensBeforeGraph;
    use crate::eval::atomics::{AtomicFence, AtomicOp, MemoryOrdering};

    #[test]
    fn program_order_edges_are_recorded_per_thread() {
        let mut graph = HappensBeforeGraph::default();
        let first = graph
            .add_atomic_op(0, AtomicOp::Store, MemoryOrdering::Release)
            .unwrap();
        let second = graph
            .add_atomic_op(0, AtomicOp::Load, MemoryOrdering::Acquire)
            .unwrap();

        assert_eq!(graph.len(), 2);
        assert_eq!(graph.edge_count(), 1);
        assert!(graph.has_edge(first, second));
        assert!(graph.happens_before(first, second));
    }

    #[test]
    fn cross_thread_release_acquire_sync_creates_happens_before() {
        let mut graph = HappensBeforeGraph::default();
        let release = graph
            .add_atomic_op(0, AtomicOp::Store, MemoryOrdering::Release)
            .unwrap();
        let acquire = graph
            .add_atomic_op(1, AtomicOp::Load, MemoryOrdering::Acquire)
            .unwrap();

        graph.add_synchronizes_with(release, acquire).unwrap();

        assert!(graph.has_edge(release, acquire));
        assert!(graph.happens_before(release, acquire));
    }

    #[test]
    fn fence_sync_propagates_prior_and_subsequent_program_order() {
        let mut graph = HappensBeforeGraph::default();
        let write = graph
            .add_atomic_op(0, AtomicOp::Store, MemoryOrdering::Relaxed)
            .unwrap();
        let release_fence = graph
            .add_fence(0, AtomicFence::new(MemoryOrdering::Release))
            .unwrap();
        let acquire_fence = graph
            .add_fence(1, AtomicFence::new(MemoryOrdering::Acquire))
            .unwrap();
        let read = graph
            .add_atomic_op(1, AtomicOp::Load, MemoryOrdering::Relaxed)
            .unwrap();

        graph
            .add_synchronizes_with(release_fence, acquire_fence)
            .unwrap();

        assert!(graph.happens_before(write, read));
    }

    #[test]
    fn invalid_cross_thread_sync_reports_both_missing_semantics() {
        let mut graph = HappensBeforeGraph::default();
        let source = graph
            .add_atomic_op(0, AtomicOp::Store, MemoryOrdering::Relaxed)
            .unwrap();
        let target = graph
            .add_atomic_op(1, AtomicOp::Load, MemoryOrdering::Relaxed)
            .unwrap();

        assert_eq!(
            graph.add_synchronizes_with(source, target),
            Err(
                "2 atomic ordering violations: cross-thread synchronization source on thread 0 needs release ordering, found `Relaxed`; cross-thread synchronization target on thread 1 needs acquire ordering, found `Relaxed`"
                    .to_string()
            )
        );
    }
}
