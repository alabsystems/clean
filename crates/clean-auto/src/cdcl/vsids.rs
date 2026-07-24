// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VSIDS (Variable State Independent Decaying Sum) decision heuristic.
//!
//! Implements a binary heap ordered by variable activity scores,
//! used by the CDCL solver to pick decision variables.

use super::types::{usize_to_u32, Var};

/// VSIDS activity-based decision heuristic data
#[derive(Clone, Debug)]
pub(super) struct VsidsData {
    /// Activity score per variable
    pub(super) activity: Vec<f64>,
    /// Activity increment (decayed over time)
    var_inc: f64,
    /// Decay factor
    var_decay: f64,
    /// Heap for variable selection (indices into activity)
    pub(super) heap: Vec<Var>,
    /// Position in heap for each variable (u32::MAX if not in heap)
    pub(super) heap_pos: Vec<u32>,
}

impl VsidsData {
    pub(super) fn new(num_vars: usize) -> Self {
        let mut heap = Vec::with_capacity(num_vars);
        let mut heap_pos = vec![0u32; num_vars];
        for (i, pos) in heap_pos.iter_mut().enumerate() {
            let idx = usize_to_u32(i, "VSIDS variable index");
            heap.push(Var::new(idx));
            *pos = idx;
        }
        Self {
            activity: vec![0.0; num_vars],
            var_inc: 1.0,
            var_decay: 0.95,
            heap,
            heap_pos,
        }
    }

    /// Bump the activity of a variable
    pub(super) fn bump(&mut self, var: Var) {
        let idx = var.index();
        self.activity[idx] += self.var_inc;

        // Rescale if activity gets too large
        if self.activity[idx] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        // Update heap position
        if self.heap_pos[idx] != u32::MAX {
            self.percolate_up(self.heap_pos[idx] as usize);
        }
    }

    /// Decay all activities
    pub(super) fn decay(&mut self) {
        self.var_inc /= self.var_decay;
    }

    /// Add a variable back to the heap
    pub(super) fn insert(&mut self, var: Var) {
        let idx = var.index();
        if self.heap_pos[idx] == u32::MAX {
            let pos = self.heap.len();
            self.heap.push(var);
            self.heap_pos[idx] = usize_to_u32(pos, "VSIDS heap position");
            self.percolate_up(pos);
        }
    }

    /// Remove and return the variable with highest activity
    pub(super) fn pop(&mut self) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let result = self.heap[0];
        self.heap_pos[result.index()] = u32::MAX;

        if self.heap.len() > 1 {
            let last = self
                .heap
                .pop()
                .expect("invariant: heap non-empty after len > 1 check");
            self.heap[0] = last;
            self.heap_pos[last.index()] = 0;
            self.percolate_down(0);
        } else {
            self.heap.pop();
        }
        Some(result)
    }

    fn percolate_up(&mut self, mut pos: usize) {
        let var = self.heap[pos];
        let act = self.activity[var.index()];

        while pos > 0 {
            let parent = (pos - 1) / 2;
            let parent_var = self.heap[parent];
            if self.activity[parent_var.index()] >= act {
                break;
            }
            self.heap[pos] = parent_var;
            self.heap_pos[parent_var.index()] =
                usize_to_u32(pos, "VSIDS heap position during percolate_up");
            pos = parent;
        }
        self.heap[pos] = var;
        self.heap_pos[var.index()] = usize_to_u32(pos, "VSIDS heap position during percolate_up");
    }

    fn percolate_down(&mut self, mut pos: usize) {
        let var = self.heap[pos];
        let act = self.activity[var.index()];

        loop {
            let left = 2 * pos + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;

            // Find child with higher activity
            let best_child = if right < self.heap.len()
                && self.activity[self.heap[right].index()] > self.activity[self.heap[left].index()]
            {
                right
            } else {
                left
            };

            if act >= self.activity[self.heap[best_child].index()] {
                break;
            }

            let child_var = self.heap[best_child];
            self.heap[pos] = child_var;
            self.heap_pos[child_var.index()] =
                usize_to_u32(pos, "VSIDS heap position during percolate_down");
            pos = best_child;
        }
        self.heap[pos] = var;
        self.heap_pos[var.index()] = usize_to_u32(pos, "VSIDS heap position during percolate_down");
    }
}
