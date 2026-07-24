// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal priority queue supporting multiple search strategies.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};

use super::types::{AesopStrategy, GoalId, Percent, SearchTree};

// =============================================================================
// Goal Priority Queue
// =============================================================================

/// Entry in the goal priority queue
#[derive(Debug, Clone)]
struct GoalQueueEntry {
    goal_id: GoalId,
    priority: Percent,
    last_expanded_in_iteration: usize,
    added_in_iteration: usize,
}

impl PartialEq for GoalQueueEntry {
    fn eq(&self, other: &Self) -> bool {
        self.goal_id == other.goal_id
    }
}

impl Eq for GoalQueueEntry {}

impl PartialOrd for GoalQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for GoalQueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher priority first (reverse ordering)
        other
            .priority
            .cmp(&self.priority)
            // Then earlier expanded (fairness)
            .then_with(|| {
                self.last_expanded_in_iteration
                    .cmp(&other.last_expanded_in_iteration)
            })
            // Then earlier added
            .then_with(|| self.added_in_iteration.cmp(&other.added_in_iteration))
    }
}

/// Goal queue supporting multiple search strategies
///
/// Uses different internal data structures based on strategy:
/// - BestFirst: BinaryHeap (priority queue)
/// - DepthFirst: Vec (stack, LIFO)
/// - BreadthFirst: VecDeque (queue, FIFO)
#[derive(Debug)]
pub struct GoalQueue {
    /// Strategy being used
    strategy: AesopStrategy,
    /// Priority queue for best-first search
    heap: BinaryHeap<GoalQueueEntry>,
    /// Stack for depth-first search (also used as queue for breadth-first)
    stack: VecDeque<GoalQueueEntry>,
}

impl GoalQueue {
    /// Create a new empty queue with default strategy (best-first)
    /// ENSURES: Returns an empty queue using `AesopStrategy::default()`.
    pub fn new() -> Self {
        Self::with_strategy(AesopStrategy::default())
    }

    /// Create a new empty queue with the given strategy
    /// ENSURES: Returns an empty queue that will pop entries according to `strategy`.
    pub fn with_strategy(strategy: AesopStrategy) -> Self {
        GoalQueue {
            strategy,
            heap: BinaryHeap::new(),
            stack: VecDeque::new(),
        }
    }

    /// Push a goal onto the queue
    /// REQUIRES: `goal_id` identifies a goal managed by the same search tree the queue will later query.
    /// ENSURES: The queued entry records the supplied priority and iteration metadata.
    pub fn push(&mut self, goal_id: GoalId, priority: Percent, last_expanded: usize, added: usize) {
        let entry = GoalQueueEntry {
            goal_id,
            priority,
            last_expanded_in_iteration: last_expanded,
            added_in_iteration: added,
        };

        match self.strategy {
            AesopStrategy::BestFirst => {
                self.heap.push(entry);
            }
            AesopStrategy::DepthFirst => {
                // LIFO: push to back, pop from back
                self.stack.push_back(entry);
            }
            AesopStrategy::BreadthFirst => {
                // FIFO: push to back, pop from front
                self.stack.push_back(entry);
            }
        }
    }

    /// Pop the next active goal according to the strategy
    ///
    /// Skips goals that are no longer active (proven or unprovable).
    /// REQUIRES: `tree` is the search tree whose `GoalId`s were previously pushed into this queue.
    /// ENSURES: Returns `Some(goal_id)` only for goals whose current `GoalState` is active.
    /// ENSURES: Inactive queued entries may be discarded while searching for the next active goal.
    pub fn pop_active_goal(&mut self, tree: &SearchTree) -> Option<GoalId> {
        match self.strategy {
            AesopStrategy::BestFirst => {
                while let Some(entry) = self.heap.pop() {
                    if let Some(goal) = tree.get_goal(entry.goal_id) {
                        if goal.state.is_active() {
                            return Some(entry.goal_id);
                        }
                    }
                }
                None
            }
            AesopStrategy::DepthFirst => {
                // LIFO: pop from back
                while let Some(entry) = self.stack.pop_back() {
                    if let Some(goal) = tree.get_goal(entry.goal_id) {
                        if goal.state.is_active() {
                            return Some(entry.goal_id);
                        }
                    }
                }
                None
            }
            AesopStrategy::BreadthFirst => {
                // FIFO: pop from front
                while let Some(entry) = self.stack.pop_front() {
                    if let Some(goal) = tree.get_goal(entry.goal_id) {
                        if goal.state.is_active() {
                            return Some(entry.goal_id);
                        }
                    }
                }
                None
            }
        }
    }
}

impl Default for GoalQueue {
    fn default() -> Self {
        Self::new()
    }
}
