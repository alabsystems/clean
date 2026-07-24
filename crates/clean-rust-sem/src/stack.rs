// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execution stack for the Rust memory model.
//!
//! Provides stack frames for local variable tracking and the call stack
//! abstraction used during Rust semantics evaluation.

use crate::memory::Address;
use crate::stacked_borrows::ProtectorId;

/// Stack frame for local variables
#[derive(Debug, Clone)]
pub struct StackFrame {
    /// Frame identifier
    pub id: u64,
    /// Local variable allocations
    pub locals: Vec<Address>,
    /// Return address placeholder
    pub return_dest: Option<Address>,
    /// Protector tokens for `&mut` arguments in this call frame.
    ///
    /// When a function receives `&mut T` parameters, each gets a protector
    /// that prevents the borrow from being invalidated for the call's duration.
    /// Released on frame pop via `OwnershipState::release_protector`.
    pub protectors: Vec<ProtectorId>,
}

impl StackFrame {
    pub fn new(id: u64) -> Self {
        Self {
            id,
            locals: Vec::new(),
            return_dest: None,
            protectors: Vec::new(),
        }
    }

    /// Add a local variable
    pub fn add_local(&mut self, addr: Address) -> u32 {
        // SAFETY: Local variable count is bounded by practical stack depth limits,
        // which are far below u32::MAX. Use saturating conversion for defense.
        let idx = u32::try_from(self.locals.len()).unwrap_or(u32::MAX);
        self.locals.push(addr);
        idx
    }

    /// Get local variable address
    pub fn get_local(&self, idx: u32) -> Option<Address> {
        self.locals.get(idx as usize).copied()
    }
}

/// Execution stack (call stack)
#[derive(Debug, Clone)]
pub struct Stack {
    frames: Vec<StackFrame>,
    next_frame_id: u64,
}

impl Stack {
    pub fn new() -> Self {
        Self {
            frames: Vec::new(),
            next_frame_id: 0,
        }
    }

    /// Push a new frame
    pub fn push_frame(&mut self) -> &mut StackFrame {
        let id = self.next_frame_id;
        self.next_frame_id += 1;
        self.frames.push(StackFrame::new(id));
        self.frames
            .last_mut()
            .expect("invariant: frame was just pushed")
    }

    /// Pop the current frame
    pub fn pop_frame(&mut self) -> Option<StackFrame> {
        self.frames.pop()
    }

    /// Get current frame
    pub fn current_frame(&self) -> Option<&StackFrame> {
        self.frames.last()
    }

    /// Get current frame mutably
    pub fn current_frame_mut(&mut self) -> Option<&mut StackFrame> {
        self.frames.last_mut()
    }

    /// Get frame at depth (0 = current)
    pub fn frame_at(&self, depth: usize) -> Option<&StackFrame> {
        let idx = self.frames.len().checked_sub(depth + 1)?;
        self.frames.get(idx)
    }

    /// Stack depth
    pub fn depth(&self) -> usize {
        self.frames.len()
    }
}

impl Default for Stack {
    fn default() -> Self {
        Self::new()
    }
}
