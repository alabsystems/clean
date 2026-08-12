// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Undo trail and scope management for MetaState backtracking (Part of #383).

use super::super::meta_id::UndoRecord;
use super::{MetaScopeMarker, MetaState, OwnedMetaScopeCloseError, OwnedMetaScopeToken};

impl MetaState {
    // ========================================================================
    // Undo Trail / Scope Management (Part of #383)
    // ========================================================================

    /// Push a new scope marker onto the undo trail.
    ///
    /// Modifications made after this call can be rolled back with `pop_scope()`.
    /// Scopes can be nested - each `pop_scope()` undoes back to the most recent
    /// `push_scope()`.
    ///
    /// # Example
    ///
    /// ```
    /// use clean_elab::MetaState;
    /// use clean_kernel::Expr;
    ///
    /// let mut state = MetaState::new();
    ///
    /// // Outer scope
    /// state.push_scope();
    /// let m1 = state.fresh(Expr::prop());
    ///
    /// // Inner scope
    /// state.push_scope();
    /// let m2 = state.fresh(Expr::prop());
    ///
    /// // Pop inner - m2 is removed, m1 still exists
    /// state.pop_scope();
    /// assert!(state.get(m1).is_some());
    /// assert!(state.get(m2).is_none()); // m2 was removed by pop_scope
    ///
    /// // Pop outer - m1 is also removed
    /// state.pop_scope();
    /// ```
    pub fn push_scope(&mut self) {
        self.scope_markers.push(MetaScopeMarker {
            undo_len: self.undo_trail.len(),
            owner: None,
        });
    }

    /// Push a scope that ordinary `pop_scope`/`commit` calls cannot consume.
    ///
    /// Only the holder of the returned private token can close this exact
    /// marker through [`Self::close_owned_scope`]. An attempted ordinary close
    /// is recorded without changing scope depth or the undo trail, allowing the
    /// owner to roll back and surface a typed invariant error.
    pub(crate) fn push_owned_scope(&mut self) -> OwnedMetaScopeToken {
        let token = loop {
            let token = OwnedMetaScopeToken(self.next_owned_scope_token);
            self.next_owned_scope_token = self.next_owned_scope_token.wrapping_add(1);
            let active = self
                .scope_markers
                .iter()
                .any(|marker| marker.owner == Some(token));
            if !active && !self.owned_scope_access_attempts.contains(&token) {
                break token;
            }
        };
        self.scope_markers.push(MetaScopeMarker {
            undo_len: self.undo_trail.len(),
            owner: Some(token),
        });
        token
    }

    /// Pop the most recent scope, undoing all modifications since the matching
    /// `push_scope()`.
    ///
    /// Returns `true` if there was a scope to pop, `false` if the scope stack
    /// was empty or the top marker is owned (in either case nothing is
    /// modified). Attempting to pop an owned marker is reported to its owner.
    pub fn pop_scope(&mut self) -> bool {
        let Some(marker) = self.scope_markers.last() else {
            return false;
        };
        if let Some(owner) = marker.owner {
            self.owned_scope_access_attempts.insert(owner);
            return false;
        }
        self.pop_top_scope_unchecked()
    }

    fn pop_top_scope_unchecked(&mut self) -> bool {
        let Some(marker) = self.scope_markers.pop() else {
            return false;
        };
        if let Some(owner) = marker.owner {
            self.owned_scope_access_attempts.remove(&owner);
        }

        // Replay undo records in reverse order
        while self.undo_trail.len() > marker.undo_len {
            if let Some(record) = self.undo_trail.pop() {
                self.apply_undo(record);
            }
        }

        true
    }

    /// Commit the current scope, keeping all modifications.
    ///
    /// This removes the most recent scope marker without undoing changes.
    /// Use this when speculative work succeeds and you want to keep the results.
    ///
    /// When all scopes are exhausted (scope_markers becomes empty), the undo trail
    /// is cleared since there's nothing left to potentially roll back to. This
    /// prevents unbounded memory growth in long-running proof searches.
    ///
    /// Returns `true` if there was a scope to commit, `false` if the scope stack
    /// was empty or the top marker is owned. Attempting to commit an owned
    /// marker is reported to its owner and changes no scope or undo state.
    pub fn commit(&mut self) -> bool {
        let Some(marker) = self.scope_markers.last() else {
            return false;
        };
        if let Some(owner) = marker.owner {
            self.owned_scope_access_attempts.insert(owner);
            return false;
        }
        self.commit_top_scope_unchecked()
    }

    fn commit_top_scope_unchecked(&mut self) -> bool {
        let Some(marker) = self.scope_markers.pop() else {
            return false;
        };
        if let Some(owner) = marker.owner {
            self.owned_scope_access_attempts.remove(&owner);
        }
        // Clean up the trail when no scopes remain (#730). At this point all
        // changes are permanent and no rollback is possible.
        if self.scope_markers.is_empty() {
            self.undo_trail.clear();
        }
        true
    }

    /// Close the exact owned scope identified by `token`.
    ///
    /// Ordinary nested scopes left above it retain the historical wrapper
    /// behavior: all are committed on success or rolled back on failure. A
    /// nested owned scope is never silently stolen. Any attempted ordinary
    /// access, missing marker, or owned obstruction is an invariant error; when
    /// the marker still exists, all work through that marker is rolled back.
    pub(crate) fn close_owned_scope(
        &mut self,
        token: OwnedMetaScopeToken,
        rollback: bool,
    ) -> Result<(), OwnedMetaScopeCloseError> {
        let Some(owned_index) = self
            .scope_markers
            .iter()
            .rposition(|marker| marker.owner == Some(token))
        else {
            return Err(OwnedMetaScopeCloseError::Missing);
        };

        let access_attempted = self.owned_scope_access_attempts.remove(&token);
        let obstructed = self.scope_markers[owned_index + 1..]
            .iter()
            .any(|marker| marker.owner.is_some());
        if access_attempted || obstructed {
            while self.scope_markers.len() > owned_index {
                let closed = self.pop_top_scope_unchecked();
                if !closed {
                    return Err(OwnedMetaScopeCloseError::Missing);
                }
            }
            return Err(if access_attempted {
                OwnedMetaScopeCloseError::AccessAttempted
            } else {
                OwnedMetaScopeCloseError::Obstructed
            });
        }

        while self.scope_markers.len() > owned_index {
            let closed = if rollback {
                self.pop_top_scope_unchecked()
            } else {
                self.commit_top_scope_unchecked()
            };
            if !closed {
                return Err(OwnedMetaScopeCloseError::Missing);
            }
        }
        Ok(())
    }

    /// Check if there are any active scopes.
    pub fn has_scope(&self) -> bool {
        !self.scope_markers.is_empty()
    }

    /// Get the current scope depth (number of nested scopes).
    pub fn scope_depth(&self) -> usize {
        self.scope_markers.len()
    }

    /// Apply an undo record, reversing its effect on the state.
    fn apply_undo(&mut self, record: UndoRecord) {
        match record {
            UndoRecord::MetaAssign { id, old_value } => {
                if let Some(meta) = self.metas.get_mut(&id) {
                    meta.assignment = old_value;
                }
            }
            UndoRecord::MetaCreate { id } => {
                self.metas.remove(&id);
            }
            UndoRecord::NextId { old_value } => {
                self.next_id = old_value;
            }
            UndoRecord::LevelConstraint { name, old_value } => {
                if let Some(val) = old_value {
                    self.level_constraints.insert(name, val);
                } else {
                    self.level_constraints.remove(&name);
                }
            }
            UndoRecord::LevelParent { name, old_parent } => {
                if let Some(parent) = old_parent {
                    self.level_parent.insert(name, parent);
                } else {
                    self.level_parent.remove(&name);
                }
            }
            UndoRecord::LevelBound { name, old_level } => {
                if let Some(level) = old_level {
                    self.level_bound.insert(name, level);
                } else {
                    self.level_bound.remove(&name);
                }
            }
            UndoRecord::LevelConcrete { name, old_level } => {
                if let Some(level) = old_level {
                    self.level_concrete.insert(name, level);
                } else {
                    self.level_concrete.remove(&name);
                }
            }
        }
    }

    /// Record an undo entry if we're in a scope.
    ///
    /// This is called internally by mutation methods to track changes.
    /// If no scope is active, this is a no-op.
    #[inline]
    pub(super) fn record_undo(&mut self, record: UndoRecord) {
        if !self.scope_markers.is_empty() {
            self.undo_trail.push(record);
        }
    }

    /// Check if the undo trail is empty (test-only accessor for private field).
    #[cfg(test)]
    pub(crate) fn is_trail_empty(&self) -> bool {
        self.undo_trail.is_empty()
    }

    /// Number of retained undo records (test-only invariant accessor).
    #[cfg(test)]
    pub(crate) fn undo_trail_len_for_tests(&self) -> usize {
        self.undo_trail.len()
    }
}
