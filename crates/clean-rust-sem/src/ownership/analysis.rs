// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{BorrowError, OwnershipState, Place, PlaceState};
use crate::types::{Lifetime, Mutability, RustType};
use std::collections::{HashMap, HashSet};

/// Borrow checker implementation
#[derive(Debug, Clone)]
pub struct BorrowChecker {
    /// Whether to enforce strict borrowing rules
    pub strict_mode: bool,
}

impl BorrowChecker {
    pub fn new() -> Self {
        Self { strict_mode: true }
    }

    /// Check if a move is valid
    pub fn check_move(&self, state: &OwnershipState, place: &Place) -> Result<(), BorrowError> {
        if state.has_any_borrow(place) {
            return Err(BorrowError::MoveWhileBorrowed {
                place: place.clone(),
            });
        }

        if state.is_moved(place) {
            return Err(BorrowError::UseAfterMove {
                place: place.clone(),
            });
        }

        if matches!(
            state.place_states.get(place),
            Some(PlaceState::Uninitialized)
        ) {
            return Err(BorrowError::UseOfUninitialized {
                place: place.clone(),
            });
        }

        Ok(())
    }

    /// Check if a borrow is valid
    pub fn check_borrow(
        &self,
        state: &OwnershipState,
        place: &Place,
        mutability: Mutability,
        _lifetime: &Lifetime,
    ) -> Result<(), BorrowError> {
        if state.is_moved(place) {
            return Err(BorrowError::UseAfterMove {
                place: place.clone(),
            });
        }

        match mutability {
            Mutability::Shared => {
                if state.has_mutable_borrow(place) {
                    return Err(BorrowError::SharedBorrowWhileMutBorrow {
                        place: place.clone(),
                    });
                }
            }
            Mutability::Mutable => {
                if state.has_any_borrow(place) {
                    if state.has_mutable_borrow(place) {
                        return Err(BorrowError::MutBorrowWhileMutBorrow {
                            place: place.clone(),
                        });
                    }
                    return Err(BorrowError::MutBorrowWhileSharedBorrow {
                        place: place.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Check if a use (read) is valid
    pub fn check_use(&self, state: &OwnershipState, place: &Place) -> Result<(), BorrowError> {
        if state.is_moved(place) {
            return Err(BorrowError::UseAfterMove {
                place: place.clone(),
            });
        }

        if matches!(
            state.place_states.get(place),
            Some(PlaceState::Uninitialized)
        ) {
            return Err(BorrowError::UseOfUninitialized {
                place: place.clone(),
            });
        }

        Ok(())
    }

    /// Check if an assignment is valid
    pub fn check_assign(
        &self,
        state: &OwnershipState,
        place: &Place,
        is_mutable: bool,
    ) -> Result<(), BorrowError> {
        if !is_mutable {
            return Err(BorrowError::AssignToImmutable {
                place: place.clone(),
            });
        }

        if state.has_any_borrow(place) {
            return Err(BorrowError::AssignWhileBorrowed {
                place: place.clone(),
            });
        }

        Ok(())
    }
}

impl Default for BorrowChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// Drop elaboration - determines when destructors run
#[derive(Debug, Clone)]
pub struct DropElaborator {
    /// Places that need to be dropped
    pending_drops: Vec<(Place, RustType)>,
}

impl DropElaborator {
    pub fn new() -> Self {
        Self {
            pending_drops: Vec::new(),
        }
    }

    /// Schedule a drop for a place
    pub fn schedule_drop(&mut self, place: Place, ty: RustType) {
        if !ty.is_copy() {
            self.pending_drops.push((place, ty));
        }
    }

    /// Get drops in order (reverse of creation)
    pub fn drain_drops(&mut self) -> Vec<(Place, RustType)> {
        let mut drops = std::mem::take(&mut self.pending_drops);
        drops.reverse();
        drops
    }
}

impl Default for DropElaborator {
    fn default() -> Self {
        Self::new()
    }
}

/// Move path analysis for tracking partial moves
#[derive(Debug, Clone, Default)]
pub struct MoveAnalysis {
    /// Places that have been fully moved
    moved: HashSet<Place>,
    /// Places that have been partially moved (with moved children)
    partial_moves: HashMap<Place, HashSet<String>>,
}

impl MoveAnalysis {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a move
    pub fn record_move(&mut self, place: &Place) {
        self.moved.insert(place.clone());

        if let Place::Field { base, field } = place {
            self.partial_moves
                .entry((**base).clone())
                .or_default()
                .insert(field.clone());
        }
    }

    /// Check if a place is fully moved
    pub fn is_moved(&self, place: &Place) -> bool {
        self.moved.contains(place)
    }

    /// Check if a place is partially moved
    pub fn is_partially_moved(&self, place: &Place) -> bool {
        self.partial_moves.contains_key(place)
    }

    /// Get moved fields of a place
    pub fn moved_fields(&self, place: &Place) -> Option<&HashSet<String>> {
        self.partial_moves.get(place)
    }
}
